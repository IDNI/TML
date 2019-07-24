# TML Installation instructions

# Requirements

  * [emscripten](https://emscripten.org/) (optionally for JS library)

# Building

## 1. Create a build directory

   The recommended way to build TML is in a separate build
   directory, for example within the top level of the TML package:

    $ mkdir build
    $ cd build

## 2. Configure

    $ cmake ../

   If everything is OK, then this should end with something like:
```
  -- Generating done
  -- Build files have been written to: /home/user/project/TML/build
```

   If CMake fails, because it cannot resolve all dependencies, then you
   may help CMake by setting some variables to help CMake locate the
   libraries. This may be done on the command-line using -Dvar=value or
   using the interactive program:

    $ ccmake ../

   or

    $ cmake-gui ../

   The GUI lists all variables that are configurable in TML's build
   process.

   The variables specify several build and configuration aspects of TML, of
   which the most relevant ones are (there are many more visible in the
   GUI):

   * CMAKE_INSTALL_PREFIX - Installation prefix for the library and include files
   * BUILD_JSLIB=1 - for building JavaScript library (requires emscripten)

## 3. Building

   To build `tml` executable and TML shared library run:

    $ make

   If you want to speed up compilation, you may want to use multiple
   threads (e.g. 4):
    $ make -j4

## 4. Install (as user with sufficient permissions):

   Install tml executable and TML shared library:

    $ make install


# Helper build scripts

  | script | description |
  | --- | --- |
  | ./release.sh [<CMAKE_OPTS>] | builds release in build-Release     |
  | ./debug.sh [<CMAKE_OPTS>] | builds debug version in build-Debug |
  | ./release-js.sh | builds release version of JS library in build-Release |
  | ./debug-js.sh | builds debug version of JS library in build-Debug |
  | ./build.sh <BUILD_TYPE> [<CMAKE_OPTS>] | builds version according to BUILD_TYPE' can be Debug (build-Debug), Release, PgoScan and PgoRun (build-Release) |
  | ./pgo_test.sh [<TEST_COMMAND_STRING>] | builds and measures a test command in Release, PgoScan and PgoRun |
