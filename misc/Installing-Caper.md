1. Get Stack (>= 1.6.1), linked from

    https://docs.haskellstack.org/en/stable/install_and_upgrade/
   
  or

    https://haskell-lang.org/get-started

  I installed it to the default location, which is somewhere in the user
  directory (not in C:\Program Files, as usual).

  Afterwards, follow this tutorial:

    https://haskell-lang.org/tutorial/stack-build

2. In the Caper directory, I executed

    stack init

  but got several complaints about missing packages. As suggested by the output
  of the previous command, I tried

    stack init --solver

  next, which succeded:

    ...
    Writing configuration to file: stack.yaml
    All done.

3. Next, I ran

    stack build --extra-include-dirs=path/to/z3/include --extra-lib-dirs=path\to\z3\bin

  which terminated with

    ...
    Registering library for caper-0.2.0.0..
    Completed 14 action(s).

  Note: I couldn't get Caper to compile against any Z3 higher than 4.5.0 (and
  some 4.5.1.nightly).

4. Afterwards, Caper.exe could be found in

    .\.stack-work\install\bf1113dd\bin\