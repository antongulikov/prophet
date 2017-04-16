// Copyright (C) 2016 Fan Long, Martin Rianrd and MIT CSAIL 
// Prophet
// 
// This file is part of Prophet.
// 
// Prophet is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
// 
// Prophet is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
// 
// You should have received a copy of the GNU General Public License
// along with Prophet.  If not, see <http://www.gnu.org/licenses/>.
#include "config.h"
#include "Utils.h"
#include "ProfileErrorLocalizer.h"
#include "BenchProgram.h"
#include "llvm/Support/CommandLine.h"
#include <queue>
#include <dirent.h>

using namespace clang;

/* Clang wrapper. */
#define CLANG_PROFILE_WRAP "pclang.py"

/* Localizer const's. */
#define LOC_LIMIT 50000

/* Maximun value not to consider. */
#define TRASHOLD 0

/* Extern from Main.cpp, parse of -cpp flag. */
extern llvm::cl::opt<bool> ForCPP;

/* Extern form Main.cpp, parse of localizer limitation. */
extern llvm::cl::opt<unsigned int> LocProcessLimit;

/**
 * Parse profile results into a map.
 * @return map assign a profile info to every source position
 */
ProfileLocationMapTy ProfileErrorLocalizer::parseProfileResult() {
    /* Lazy assign of location index. */
    if (LI == NULL)
        LI = new LocationIndex(INDEX_FILE);

    /* Map def. */
    ProfileLocationMapTy M;
    M.clear();

    /* Open results cycle. */
    DIR *dp = opendir("/tmp");
    struct dirent *dirp;
    while (((dirp = readdir(dp)))) {
        /* Nstr. */
        std::string nstr = dirp->d_name;

        /* Skip wrong file. */
        if ((nstr.substr(0, 5) != "__run") || (nstr.substr(nstr.size() - 4, 4) != ".log"))
            continue;

        /* Open fin. */
        std::ifstream fin(("/tmp/" + nstr).c_str(), std::ifstream::in);
        std::string line1, line2;

        /* Parse pid. */
        std::string pid = nstr.substr(5, nstr.size() - 4 - 5);

        /* We get an empty pid. */
        if (pid == "") {
            fprintf(stderr, "Cannot get pid value, assume 0.");
            llvm::errs() << nstr << "\n";
            assert(0);
            pid = "0";
        }

        /* Parsing. */
        while (std::getline(fin, line1)) {
            /* Dealing with lines. */
            if (line1 == "") break;
            std::getline(fin, line2);
            SourcePositionTy tmploc;
            {
                std::istringstream sin(line1);
                unsigned long idx;
                sin >> idx;
                tmploc = LI->getProfileLocation(idx);

                /* Previous filepath. */
                tmploc.expFilename = P.normalizePath(tmploc.expFilename);

                /* Trimed filepath. */
                tmploc.spellFilename = P.normalizePath(tmploc.spellFilename);
            }

            /* Parsing values. */
            long long cnt, cnt2;
            {
                std::istringstream sin(line2);
                sin >> cnt >> cnt2;
            }

            /* Main part. */
            RoundInfoTy tmp;
            tmp.execution_cnt = cnt;
            tmp.beforeend_cnt = cnt2;
            tmp.pid = pid;
            M[tmploc].rounds.push_back(tmp);
        }

        /* Closing fin. */
        fin.close();
    }

    /* Closing dp. */
    closedir(dp);

    /* Return result. */
    return M;
}

/**
 * Clearing profile results.
 */
void ProfileErrorLocalizer::clearProfileResult() {
    int res = system("rm -rf /tmp/__run*.log");
    assert(res == 0);
}

/**
 * Calc average value.
 */
template<typename T>
double avg_double(const std::vector<T> &v, size_t k = 1) {
    if (v.size() == 0) {
        return 0;
    } else {
        double s = 0;
        for (size_t i = 0; i < v.size(); i++) {
            double ls = 1;
            for (size_t j = 0; j < k; j++) {
                ls *= (double) v[i];
            }
            s += ls;
        }
        return s / v.size();
    }
}

/**
 * Map RoundInfoTy to vec of long long of beforeend_cnt.
 */
std::vector<long long> toVecOfBEC(const std::vector<RoundInfoTy> &v) {
    std::vector<long long> r;
    r.clear();
    for (size_t i = 0; i < v.size(); i++) {
        r.push_back(v[i].beforeend_cnt);
    }
    return r;
}

/* Tmp struct for score. */
typedef struct {
    long long execution_cnt;
    std::vector<double> beforeend_cnts;
    std::string pid;
} TmpInfoTy;

/* Tmp map. */
typedef std::map<SourcePositionTy, TmpInfoTy> TmpLocationMapTy;

/**
 * Compute beforeend_cnt part of score.
 */
double compute_b_score(const std::vector<double> &b, size_t k) {
    std::vector<double> v;
    v.clear();
    for (size_t i = 0; i < b.size(); i++) {
        v.push_back(b[i] + 1);
    }
    double res = avg_double(v, k);
    if (res == 0) {
        return 0;
    } else {
        return 1.0 / res;
    }
}

/**
 * Another version of computing score.
 */
double compute_b_score_exp(const std::vector<double> &b) {
    std::vector<double> v;
    v.clear();
    for (size_t i = 0; i < b.size(); i++) {
        v.push_back(b[i] * exp(-b[i]));
    }
    double avg = avg_double(v);
    return exp(-avg);
}

/**
 * Yet another version of computing score.
 */
double compute_b_score_exp2(const std::vector<double> &b) {
    double t = 0, w = 0;
    for (size_t i = 0; i < b.size(); i++) {
        double weight = exp(-b[i]);
        w += weight;
        t += b[i] * exp(-b[i]);
    }
    if (w == 0) {
        return 0;
    } else {
        return exp(-t / (8 * w));
    }
}

/**
 * Computing score for loc's localizer ranging.
 */
double compute_score(const TmpInfoTy &n, const TmpInfoTy &p, double negs, double poss) {
    double NEG = (((double) n.execution_cnt) / negs) + compute_b_score_exp2(n.beforeend_cnts);
    double POS = (((double) p.execution_cnt) / poss) + compute_b_score_exp2(p.beforeend_cnts);
    return NEG - POS;
}

/**
 * Run error localization on bugged files, skip build if skip_build, using BenchProgram P. Constructor.
 * @param P bench prog obj
 * @param bugged_files set of bugged files with error
 * @param skip_build true if we should skip building the src
 */
ProfileErrorLocalizer::ProfileErrorLocalizer(BenchProgram &P,
                                             const std::set<std::string> &bugged_files,
                                             bool skip_build) :
        P(P), negative_cases(P.getNegativeCaseSet()), positive_cases(P.getPositiveCaseSet()) {
    /* We will assign LI later. */
    LI = NULL;

    /* Dealing with building the profile close of src. */
    if (skip_build) { /* If we value of skip_build true: */
        /* We already have "profile" clone of "src", so just add it into map. */
        P.addExistingSrcClone("profile", true);
    } else { /* Else just build it. */
        /* Making a clone of src. */
        P.clearSrcClone("profile");
        P.createSrcClone("profile");

        /* Making map of env vars. */
        BenchProgram::EnvMapTy envMap;
        envMap.clear();
        if (ForCPP.getValue())
            envMap["COMPILE_CMD"] = "clang++";
        else
            envMap["COMPILE_CMD"] = CLANG_CMD;
        envMap["INDEX_FILE"] = INDEX_FILE;

        /* Clearing ./tmp/ files. */
        int ret = system("rm -rf /tmp/__* /tmp/pclang*");
        assert(ret == 0);

        /* Building a profile with wrapper. */
        P.buildSubDir("profile", CLANG_PROFILE_WRAP, envMap);
    }

    /* Limit. */
    unsigned int limit = LocProcessLimit.getValue();

    /* We test with an unmodified environment. */
    BenchProgram::EnvMapTy testEnv;
    testEnv.clear();

    /* Negative marks data structure. */
    TmpLocationMapTy negative_mark;
    negative_mark.clear();

    /* Neg count. */
    size_t cnt = 0;
    size_t min_neg = 1000000;
    for (TestCaseSetTy::const_iterator it = negative_cases.begin(); it != negative_cases.end(); ++it) {
        /* Break if reach limit. */
        if (cnt >= limit) break;

        /* Info. */
        llvm::errs() << "Neg Processing: " << *it << "\n";

        /* Update min. */
        if (*it < min_neg) min_neg = *it;

        /* Process of profiling. */
        ProfileLocationMapTy res;
        clearProfileResult();
        bool tmp = P.test("profile", *it, testEnv, true);
        res = parseProfileResult();

        /* Check that test is negative. */
        assert(!tmp);

        /* Iterate though profile loc map. */
        for (ProfileLocationMapTy::iterator iit = res.begin(); iit != res.end(); ++iit) {
            if (negative_mark.count(iit->first) != 0) { /* If already in map - inc. */
                negative_mark[iit->first].execution_cnt++;
            } else { /* Else - initial profile info. */
                negative_mark[iit->first].execution_cnt = 1;
            }

            /* Calc some values. */
            negative_mark[iit->first].beforeend_cnts.push_back(
                    avg_double(toVecOfBEC(iit->second.rounds)));
            negative_mark[iit->first].pid = iit->second.rounds.at(0).pid;
        }

        /* Inc. */
        cnt++;
    }

    /* Total amount of negative cases. */
    double negs = (double) cnt;

    /* Positive mark data structure. */
    TmpLocationMapTy positive_mark;
    positive_mark.clear();

    /* Pos count. */
    cnt = 0;
    for (TestCaseSetTy::const_iterator it = positive_cases.lower_bound(min_neg - (limit / 2));
         it != positive_cases.end(); ++it) {
        /* Break if reach limit. */
        if (cnt >= limit) break;

        /* Info. */
        llvm::errs() << "Pos processing: " << *it << "\n";

        /* Process of profiling. */
        ProfileLocationMapTy res;
        clearProfileResult();
        bool tmp = P.test("profile", *it, testEnv, true);
        res = parseProfileResult();

        /* Bad tmp. */
        if (!tmp) {
            fprintf(stderr, "Profile version failed on this, maybe because of timeout due to overhead!\n");
            continue;
        }

        /* Iterate though profile loc map. */
        for (ProfileLocationMapTy::iterator iit = res.begin(); iit != res.end(); ++iit) {
            if (positive_mark.count(iit->first) != 0) { /* If already in map - inc and calc. */
                positive_mark[iit->first].execution_cnt++;
            } else { /* Else - initial profile info. */
                positive_mark[iit->first].execution_cnt = 1;

            }

            /* Calc some values. */
            positive_mark[iit->first].beforeend_cnts.push_back(
                    avg_double(toVecOfBEC(iit->second.rounds)));
            positive_mark[iit->first].pid = iit->second.rounds.at(0).pid;
        }

        /* Inc. */
        cnt++;
    }

    /* Total amount of positive cases. */
    double poss = (double) cnt;

    /* Filter only interesting locs. */
    TmpLocationMapTy interestingLocs;
    interestingLocs.clear();
    if (bugged_files.size() == 0) {
        interestingLocs = negative_mark;
    } else {
        for (TmpLocationMapTy::iterator it = negative_mark.begin(); it != negative_mark.end(); ++it) {
            if (bugged_files.count(it->first.expFilename) == 1) {
                interestingLocs.insert(std::make_pair(it->first, it->second));
            }
        }
    }

    /* Priority queue for sort. Triple of score, loc, pid. */
    std::priority_queue<std::pair<double, std::pair<SourcePositionTy, std::string> > > Q;

    for (TmpLocationMapTy::iterator it = interestingLocs.begin(); it != interestingLocs.end(); ++it) {
        /* Skip if header. */
        if (isSystemHeader(it->first.expFilename)) {
            continue;
        }

        /* Push new value. */
        TmpInfoTy p;
        std::vector<double> v;
        v.clear();
        if (positive_mark.count(it->first) == 0) {
            p.execution_cnt = 0;
            p.beforeend_cnts = v;
            p.pid = "";
        } else {
            p = positive_mark[it->first];
        }
        Q.push(std::make_pair(compute_score(it->second, p, negs, poss), std::make_pair(it->first, it->second.pid)));

        /* Size < LOC_LIMIT. */
        while (Q.size() > LOC_LIMIT) Q.pop();
    }

    /* Printf. Need to be deleted. //TODO */
    outlog_printf(1, "negs: %lf poss: %lf\n", negs, poss);

    /* Get result. */
    while (Q.size() > 0) {
        ResRecordTy tmp;
        tmp.score = Q.top().first;
        tmp.loc = Q.top().second.first;
        tmp.pid = Q.top().second.second;

        if (tmp.score > TRASHOLD) {
            bool exists = false;
            for (size_t i = 0; i < candidateResults.size(); ++i) {
                if (candidateResults.at(i) == tmp) {
                    exists = true;
                    break;
                }
            }
            if (!exists) {
                candidateResults.push_back(tmp);
            }
        }

        /* Delet. */
        Q.pop();

        /* Printf. Need to be deleted. //TODO */
        outlog_printf(1, "(-) %d | ", negative_mark[tmp.loc].execution_cnt);
        for (size_t i = 0; i < negative_mark[tmp.loc].beforeend_cnts.size(); i++) {
            outlog_printf(1, "%lf ", negative_mark[tmp.loc].beforeend_cnts[i]);
        }
        outlog_printf(1, " | (+) %d | ", positive_mark[tmp.loc].execution_cnt);
        for (size_t i = 0; i < positive_mark[tmp.loc].beforeend_cnts.size() && i < 10; i++) {
            outlog_printf(1, "%lf ", positive_mark[tmp.loc].beforeend_cnts[i]);
        }
        outlog_printf(1, "\n");
    }

    /* Print result. */
    printResult(P.getLocalizationResultFilename());
}

/**
 * Create and get an array of candidate locs.
 * @return array of candidate locs
 */
std::vector<SourcePositionTy> ProfileErrorLocalizer::getCandidateLocations() {
    std::vector<SourcePositionTy> ret;
    ret.clear();
    for (size_t i = 0; i < candidateResults.size(); i++)
        ret.push_back(candidateResults[i].loc);
    return ret;
}

/**
 * Print result to file.
 * @param outfile file to print in
 */
void ProfileErrorLocalizer::printResult(const std::string &outfile) {
    std::ofstream fout(outfile.c_str(), std::ofstream::out);
    assert(fout.is_open());
    for (size_t i = 0; i < candidateResults.size(); ++i) {
        ResRecordTy tmp = candidateResults[i];
        fout << tmp.loc << "\t\t" << tmp.score << "\t\t" << tmp.pid << "\n";
    }
    fout.close();
}

/**
 * Construct an error localizer from already existing file.
 * @param P bench prog obj
 * @param res_file file with localization results
 */
ProfileErrorLocalizer::ProfileErrorLocalizer(BenchProgram &P, const std::string &res_file)
        : P(P), negative_cases(P.getNegativeCaseSet()), positive_cases(P.getPositiveCaseSet()) {
    LI = NULL;
    std::ifstream fin(res_file.c_str(), std::ifstream::in);
    assert(fin.is_open());
    ResRecordTy tmp;
    candidateResults.clear();
    std::string line = "";
    size_t cnt = 0;
    while (std::getline(fin, line)) {
        cnt++;
        if (line == "")
            continue;
        std::istringstream sin(line);
        sin >> tmp.loc;
        sin >> tmp.score >> tmp.pid;
        if (tmp.pid == "") {
            fprintf(stderr, "Corrupted file at line %lu, assume pid 0\n", (unsigned long) cnt);
            tmp.pid = "0";
        }
        candidateResults.push_back(tmp);
    }
    fin.close();
}
