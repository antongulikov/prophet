cmake_minimum_required(VERSION 3.7)
project(prophet_src)

set(CMAKE_CXX_STANDARD 11)

set(SOURCE_FILES
        _prophet_profile.cpp
        _prophet_profile.h
        _test_runtime.cpp
        ASTDiffer.cpp
        ASTDiffer.h
        ASTDifferTest.cpp
        ASTUtils.cpp
        ASTUtils.h
        BenchProgram.cpp
        BenchProgram.h
        CodeRewrite.cpp
        CodeRewrite.h
        config.h
        ConfigFile.h
        DuplicateDetector.cpp
        DuplicateDetector.h
        ErrorLocalizer.cpp
        ErrorLocalizer.h
        ExprSynthesizer.cpp
        ExprSynthesizer.h
        FeatureExtract.cpp
        FeatureParameter.h
        FeatureVector.h
        GlobalAnalyzer.cpp
        GlobalAnalyzer.h
        learner.cpp
        LocalAnalyzer.cpp
        LocalAnalyzer.h
        Main.cpp
        pdiffer.cpp
        PlayGround.cpp
        ProfileErrorLocalizer.cpp
        ProfileErrorLocalizer.h
        ProfilerAction.cpp
        RepairCandidateGenerator.cpp
        RepairCandidateGenerator.h
        RepairSearchEngine.cpp
        RepairSearchEngine.h
        SourceContextManager.cpp
        SourceContextManager.h
        Utils.cpp
        Utils.h)

add_executable(prophet_src ${SOURCE_FILES})