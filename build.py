#!/usr/bin/env python
from os import system

if __name__ == "__main__":
    system("docker cp ./. $(docker ps -aq):/home/ubuntu/Workspace/prophet/src/")
    system("docker exec -u=\"root\" --privileged --tty $(docker ps -aq) chown -R ubuntu:ubuntu /home/ubuntu/Workspace/prophet/src")
    system("docker exec --tty $(docker ps -aq) python /home/ubuntu/Workspace/prophet/cmd build")
