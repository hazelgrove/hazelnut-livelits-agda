# hazel-livelits-agda
This repository is the mechanization of our ongoing work on livelits. The
starting point is the dynamics developed in our in our [POPL19
paper](https://arxiv.org/pdf/1805.00155), mechanized
[here](https://github.com/hazelgrove/hazelnut-dynamics-agda). This
mechanization is paired with [this
paper](https://github.com/hazelgrove/livelits-paper), which is to appear at
to [PLDI21](https://pldi21.sigplan.org/).

# How To Check These Proofs

These proofs are known to check under `Agda version 2.6.1`. The most
direct, if perhaps not the easiest, option to check the proofs is to
install that version of Agda or one compatible with it, download the code
in this repo, and run `agda all.agda` at your command line.

Alternatively, we have provided a [Docker file](Dockerfile) to make it
easier to build that environment and check the proofs. Note that this only
checks the proofs in `2.6.1-1build1` because that is the most recent
version available via `apt-get` at the time of writing of this README; more
recent versions of Agda have been released, but they don't differ in ways
that are material to this work and greatly increase the complexity and time
it takes to check the proofs in a containerized environment.

To use the Dockerfile, first install
[Docker](https://www.docker.com/products/docker-desktop), make sure the
Docker daemon is running, and clone this repository to your local
machine. Then, at a command line inside that clone, run

```
docker build -t hazel-livelit .
```

The first time you run this it may take a fair amount of time as Docker
installs Agda on top of a base Ubuntu image (something like 200 sec), but
subsequent runs after small changes to the Agda files will be much
faster. When it finishes, run

```
docker run hazel-livelit
```

This should take less than a minute, produce a line of output per agda file
as Agda checks each module, and then exit without producing an error.

Note that the `docker build` command copies the files from your host
machine into the virtual one, so if you modify them and then just rerun the
`docker run` command without rerunning `docker build`, you will be checking
stale files.

Example output of each of these two steps is shown here, although the exact
output may differ on your machine slightly:

```
pldi@bruce Desktop % git clone git@github.com:hazelgrove/hazelnut-livelits-agda.git
Cloning into 'hazelnut-livelits-agda'...
remote: Enumerating objects: 168, done.
remote: Counting objects: 100% (168/168), done.
remote: Compressing objects: 100% (98/98), done.
remote: Total 2246 (delta 102), reused 117 (delta 70), pack-reused 2078
Receiving objects: 100% (2246/2246), 498.71 KiB | 3.59 MiB/s, done.
Resolving deltas: 100% (1560/1560), done.
pldi@bruce Desktop % cd hazelnut-livelits-agda
pldi@bruce hazelnut-livelits-agda % docker build -t hazel-livelit .
[+] Building 150.7s (10/10) FINISHED
 => [internal] load build definition from Dockerfile                                                                     0.0s
 => => transferring dockerfile: 452B                                                                                     0.0s
 => [internal] load .dockerignore                                                                                        0.0s
 => => transferring context: 2B                                                                                          0.0s
 => [internal] load metadata for docker.io/library/ubuntu:groovy                                                         1.1s
 => [internal] load build context                                                                                        0.0s
 => => transferring context: 6.31kB                                                                                      0.0s
 => [1/5] FROM docker.io/library/ubuntu:groovy@sha256:37586e1b9bab0a851b639c9102b002475987c336fa3433fa01b6abf98dfdc2a7   0.0s
 => CACHED [2/5] RUN apt-get -qy update                                                                                  0.0s
 => [3/5] RUN apt-get -qy install agda=2.6.1-1build1                                                                   125.7s
 => [4/5] COPY . .                                                                                                       0.1s
 => [5/5] RUN ["rm", "-f", "*.agdai"]                                                                                    0.4s
 => exporting to image                                                                                                  23.1s
 => => exporting layers                                                                                                 23.1s
 => => writing image sha256:1b3b91eb0e74ebfdec236b799e73c5e3940bb99b7d5530f0f83610d67354aee6                             0.0s
 => => naming to docker.io/library/hazel-livelit                                                                         0.0s
pldi@bruce hazelnut-livelits-agda % docker run hazel-livelit
Checking all (/all.agda).
 Checking Nat (/Nat.agda).
  Checking Prelude (/Prelude.agda).
 Checking List (/List.agda).
 Checking contexts (/contexts.agda).
 Checking core (/core.agda).
 Checking lemmas-gcomplete (/lemmas-gcomplete.agda).
 Checking disjointness (/disjointness.agda).
  Checking lemmas-disjointness (/lemmas-disjointness.agda).
  Checking dom-eq (/dom-eq.agda).
 Checking holes-disjoint-checks (/holes-disjoint-checks.agda).
 Checking lemmas-freshness (/lemmas-freshness.agda).
 Checking finality (/finality.agda).
  Checking progress-checks (/progress-checks.agda).
   Checking lemmas-consistency (/lemmas-consistency.agda).
   Checking type-assignment-unicity (/type-assignment-unicity.agda).
   Checking lemmas-progress-checks (/lemmas-progress-checks.agda).
 Checking focus-formation (/focus-formation.agda).
 Checking ground-decidable (/ground-decidable.agda).
 Checking grounding (/grounding.agda).
 Checking lemmas-subst-ta (/lemmas-subst-ta.agda).
  Checking weakening (/weakening.agda).
   Checking exchange (/exchange.agda).
   Checking lemmas-freshG (/lemmas-freshG.agda).
  Checking binders-disjoint-checks (/binders-disjoint-checks.agda).
 Checking typ-dec (/typ-dec.agda).
 Checking lemmas-ground (/lemmas-ground.agda).
 Checking lemmas-matching (/lemmas-matching.agda).
 Checking synth-unicity (/synth-unicity.agda).
 Checking elaborability (/elaborability.agda).
 Checking elaboration-generality (/elaboration-generality.agda).
 Checking elaboration-unicity (/elaboration-unicity.agda).
 Checking typed-elaboration (/typed-elaboration.agda).
 Checking canonical-boxed-forms (/canonical-boxed-forms.agda).
  Checking canonical-value-forms (/canonical-value-forms.agda).
 Checking canonical-indeterminate-forms (/canonical-indeterminate-forms.agda).
 Checking preservation (/preservation.agda).
 Checking progress (/progress.agda).
 Checking cast-inert (/cast-inert.agda).
  Checking lemmas-complete (/lemmas-complete.agda).
 Checking complete-elaboration (/complete-elaboration.agda).
 Checking complete-preservation (/complete-preservation.agda).
 Checking complete-progress (/complete-progress.agda).
 Checking contraction (/contraction.agda).
 Checking continuity (/continuity.agda).
 Checking typed-expansion (/typed-expansion.agda).
 Checking lemmas-freevars (/lemmas-freevars.agda).
 Checking livelit-reasoning-principles (/livelit-reasoning-principles.agda).
pldi@bruce hazelnut-livelits-agda %
```


# Editing These Proofs

Instructions for setting up `agda-mode` for emacs can be found
[here](https://agda.readthedocs.io/en/v2.6.1.3/tools/emacs-mode.html). This
is, roughly speaking, the canonical way to view and edit Agda programs.

Most text editors that support Agda can be configured to use the version
instead a Docker container instead of your host machine, so you can
experiment with or evolve this code without making too much of a mess. For
some example instructions, see [the docker-agda
repo](https://github.com/banacorn/docker-agda).

# How To Connect The Paper To This Mechanization

Generally, files are named after the theorems that they prove. In
particular, the theorems, figures, and definitions mentioned explicitly in
Section 4 can be found as follows:

* The contents of Figure 4 can be found in
  [core.agda:7-107](core.agda#L7-L107). Note that the notation for product
  types in the mechanization is `⊗` rather than `×` and that sums and
  recursive types are not present in the mechanization. It would be
  straightforward to add them, but doing so would only make the
  mechanization larger not more instructive so we have omitted them
  here. Sums and recursive types are included in the paper since they would
  be required to encode the syntax in the language in the standard way; in
  the mechanization we instead postulate that such an encoding exists to be
  able to state the rules that mention it without proving anything about it
  explictly.

* Theorem 4.1, "Typed Elaboration", is proven in
  [typed-elaboration.agda](typed-elaboration.agda).

* Theorem 4.2, "Preservation", is proven in
  [preservation.agda](preservation.agda). `d final` is given at
  [core.agda:536-538](core.agda#L536-L538) and `d1 ⇓ d2` is given at
  [core.agda:859-860](core.agda#L859-L860).

* The contents of Figure 5 can be found in
  [core.agda:903-973](core.agda#L903-L973).

* Definition 4.3, "Livelit Context Well-Formedness", is given in a
  functional style rather than a declarative one at
  [core.agda:880-889](core.agda#L880-L889).

* The rule `EApLiveLit` discussed at length in Section 4.2.2 is given by
  `SPEApLivelit` at [core.agda:947-956](core.agda#L947-L956).

* Theorem 4.4, "Typed Expansion", is proven in
  [typed-expansion.agda](typed-expansion.agda).

Note that, as stated in the paper, the theorems and definitions past
Theorem 4.4 are not currently mechanized.

`all.agda` acts a bit like an ad hoc `Makefile` in that it imports every
other file in the repository; running `agda all.agda` and not getting any
errors shows that everything checks as written.

Files with names that begin with `lemma-` generally contain lemmas and
helper theorems that, while true and required, are more technical in nature
than particularly interesting. `Prelude.agda` contains shorthand and
idiomatic notation specific to this development; `List.agda` and `Nat.agda`
are similar but define the standard types for lists and unary
naturals. This was done to avoid dependency on a particular version of any
one standard library or another, since the things we need are modest.
