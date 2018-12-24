# hazel-palette-agda
This repository is the mechanization of our ongoing work on palettes. The
starting point is the dynamics developed in our in our [POPL19
paper](https://arxiv.org/pdf/1805.00155), mechanized
[here](https://github.com/hazelgrove/hazelnut-dynamics-agda).

# How To Check These Proofs

These proofs are known to check under `Agda 2.5.4.2`. The most direct, if
not the easiest, option to check the proofs is to install that version of
Agda or one compatible with it, download the code in this repo, and run
`agda all.agda` at the command line.

Alternatively, we have provided a [Docker file](Dockerfile) to make it
easier to build that environment and check the proofs. To use it, first
install [Docker](https://www.docker.com/products/docker-desktop), make sure
the Docker daemon is running, and clone this repository to your local
machine. Then, at a command line inside that clone, run

```
docker build -t hazel-palette .
```

This may take a fair amount of time. When it finishes, run

```
docker run hazel-palette
```

This should take less than a minute, produce a lot of output as Agda checks
each module and function, and end with either the line `Finished all.` or
`Loading all (/all.agdai).` to indicate success, depending on Docker-level
caching.

Most text editors that support Agda can be configured to use the version
instead a Docker container instead of your host machine, so you can
experiment with or evolve this code without making too much of a mess. For
some example instructions, see [the docker-agda
repo](https://github.com/banacorn/docker-agda).
