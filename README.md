# hazel-livelits-agda
This repository is the mechanization of our ongoing work on livelits,
supporting our submission to PLDI 2021.

# How To Check These Proofs

These proofs are known to check under `Agda version 2.6.1`. The most
direct, if not the easiest, option to check the proofs is to install that
version of Agda or one compatible with it, download the code in this repo,
and run `agda all.agda` at the command line.

Alternatively, we have provided a [Docker file](Dockerfile) to make it
easier to build that environment and check the proofs. Note that this only
checks the proofs in `2.6.0.1-1build4` because that is the most recent
version available via `apt-get` at the time of writing of this README.

To use it, first install
[Docker](https://www.docker.com/products/docker-desktop), make sure the
Docker daemon is running, and clone this repository to your local
machine. Then, at a command line inside that clone, run

```
docker build -t hazel-livelit .
```

This may take a fair amount of time as Docker installs Agda on top of a
base Ubuntu image. When it finishes, run

```
docker run hazel-livelit
```

This should take less than a minute, produce a lot of output as Agda checks
each module and function, and then exit without producing an error.

# Editing These Proofs

Most text editors that support Agda can be configured to use the version
instead a Docker container instead of your host machine, so you can
experiment with or evolve this code without making too much of a mess. For
some example instructions, see [the docker-agda
repo](https://github.com/banacorn/docker-agda).

# Where To Start Reading

The definitions and encodings of the mathematical objects from the paper
are all in `core.agda`, so that is the place to start. Each theorem is
broken out in to a file and module named after that theorem. Files with
`lemmas` or `checks` in their names are generally uninteresting in that
they contain lemmas and small theorems that must be proven in order to make
the particular encoding of things correct, but are often unsurprising,
obscure, or both. They should be read as needed, really only if a
particular use is puzzling. `Prelude.agda`, `Nat.agda` and `List.agda`
define some standard types, some theorems on them, and some notation used
throughout.
