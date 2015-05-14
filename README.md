# EPIT2015: Your research in Coq

## Description

During the last session of the school, participants will work on the
mechanization of their specific research domain with the help of the
pedagogical team of the school. A single session of 3 hours is for
sure not enough to mechanize an entire research domain! The purpose of
this session (and actually of the entire school) is to get you started
to work with Coq on a first small project of your own to be continued
after the school. To maximise the odds to achieve this objective, we
want to help by advising you as early as possible about how your
problem should probably be mechanized in Coq. For this reason, we ask
you to prepare your project using the instructions of the next section.

## Instructions

If for some reasons, you cannot follow these instructions, look at
the email-based instructions instead (see the next section). If you
need help, please contact `yrg@pps.univ-paris-diderot.fr`.

- Create an account on [GitHub](http://github.com) and send your
  login by email to `yrg@pps.univ-paris-diderot.fr` so that we
  can give you the permissions to push on the repository.

- Make sure the `git` control version system is installed on your system.

- In a terminal, clone the repository on your local file system:

```
git clone git@github.com:yurug/coqepit.git
```

This will create a folder coqepit.git.

- In a terminal, create a subfolder for your project in the folder `coqepit.git`:

```
mkdir your-name
```

- In that folder, create a file named README.md describing a proof
  you know well and that you want to mechanize within Coq and add
  it to your repository.

```
git add README.md
```

- Commit your file:

```
git commit -a -m 'README.md: Update.'
```

- and push your changes to the github repository:

```
git push origin master
```

If you need usage documentation about git, you can try:

[A crash course](https://earlyandoften.wordpress.com/2012/05/03/git-crashcourse/)
[The official GIT tutorial](http://git-scm.com/docs/gittutorial][The official GIT tutorial)

## Mail-based instructions

Using the github repository would ease the interaction between you and
the pedagogical team. Nevertheless, you can always send us a description
of a proof you know well and that you want to mechanize within Coq by
sending an email to `yrg@pps.univ-paris-diderot.fr`.