# Using Stack (Windows 10)

**IMPORTANT**: This worked in winter 2018/19 for CAV'19, but no longer succeeded in winter 2019/20 for CAV'20.

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



# Using Cabal (Windows 10)

**IMPORTANT**: I've tried this in winter 2019/20 for CAV'20, but it ultimately didn't work.

1. Checked out Caper sources

1. Installed Haskell Platform 8.0.1:
   * https://www.haskell.org/platform/prior.html
   * https://www.haskell.org/platform/download/8.0.1/HaskellPlatform-8.0.1-full-x86_64-setup-a.exe

1. Open a command Window:

    ```text
    D:\Develop\caper-cav19>ghc --version
    
    The Glorious Glasgow Haskell Compilation System, version 8.0.1
    ```

    ```text
    D:\Develop\caper-cav19>cabal --version

    cabal-install version 1.24.0.0
    compiled using version 1.24.0.0 of the Cabal library    
    ```

1. Opened command window in Caper source directory and followed Caper's `README.md`:

    ```text
    D:\Develop\caper-cav19>cabal sandbox init
    
    Writing a default package environment file to
    D:\Develop\caper-cav19\cabal.sandbox.config
    Creating a new sandbox at D:\Develop\caper-cav19\.cabal-sandbox
    ```

    ```text
    D:\Develop\caper-cav19>cabal update
    
    Downloading the latest package list from hackage.haskell.org
    ```

    Attention: in the next command, make sure to *remove trailing backslashes* from the Z3 paths. 

    ```text
    D:\Develop\caper-cav19>cabal install --dependencies-only --extra-include-dirs=C:\Program_Files_Portable\-z3_4.5.0_x64-win\include --extra-lib-dirs=C:\Program_Files_Portable\-z3_4.5.0_x64-win\bin

    Resolving dependencies...
    Notice: installing into a sandbox located at
    D:\Develop\caper-cav19\.cabal-sandbox
    Configuring FloatingHex-0.4...
    Configuring SafeSemaphore-0.10.1...
    Configuring clock-0.8...
    ...
    Installed sbv-8.0
    ```

    The next step didn't succeed:

    ```text
    D:\Develop\caper-cav19>cabal configure --enable-tests

    Resolving dependencies...
    Warning: solver failed to find a solution:
    Could not resolve dependencies:
    rejecting: caper-0.2.0.0:!test (constraint from config file, command line
    flag, or user target requires opposite flag selection)
    trying: caper-0.2.0.0:*test
    unknown package: either (dependency of caper-0.2.0.0:*test)
    Dependency tree exhaustively searched.
    Trying configure anyway.
    Configuring caper-0.2.0.0...
    cabal: Encountered missing dependencies:
    either -any, tasty -any, tasty-hunit -any, tasty-quickcheck -any    
    ```

    Instead, I tried without `--enable-tests`:

    ```text
    D:\Develop\caper-cav19>cabal configure

    Resolving dependencies...
    Configuring caper-0.2.0.0...
    ```

    The last step, `cabal build`, always failed, though, despite trying loads of different Haskell Platform and Stack versions :-(