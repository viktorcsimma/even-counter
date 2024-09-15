# AcornCalc

A graphical exact-real calculator written in Qt
that is based the [Acorn](https://github.com/viktorcsimma/acorn) library,
capable of printing results with an arbitrary precision.

## Binary distribution

Binaries can be downloaded both
[for Linux](https://csimmaviktor.web.elte.hu/calc_linux.zip) and
[for Windows](https://csimmaviktor.web.elte.hu/calc_windows.zip).
After extracting the appropriate ZIP file, AcornCalc can be started
by running `calc.sh` or `calc.exe`.

## Building from source

You will need:
- Acorn (see instructions [there](https://github.com/viktorcsimma/acorn))
- Catch2 (for the tests)
- Qt (built from source, with the _correct compiler_ and the `-static` and `-bundled-xcb-xinput` options – see later)

**Note:** it is essential that everything gets compiled with the _same_ C compiler,
including Acorn, Qt and AcornCalc itself.
On Linux, this does not pose a problem,
as GHC uses the default compiler of the system.
On Windows, however, GHC 9.4.8 depends on Clang 14 as its C backend;
so if you want to use a version of Acorn built with it,
you need to download the version of [llvm-mingw](https://github.com/mstorsjo/llvm-mingw/releases)
based on LLVM 14.0.0
and build Qt from source with it
(see instructions in [this tutorial](https://doc.qt.io/qt-6/windows-building.html)).
(Another option is to make GHC use a user-specified backend;
I have not tried that yet.)

I recommend Qt Creator for starting the build process.
Create the kit with the appropriate C/C++ compilers
and the Qt binaries built with them.

## Deployment

For me, the most sympathetic solution was to link the executable statically
so that it becomes as portable as possible.

### Ubuntu

On Ubuntu, you have to install the packages listed
in [this article](https://doc.qt.io/qt-6/linux-requirements.html)
of the documentation
(the part after _"we recommend that you install the following packages..."_).
Only _then_ should you proceed with building Qt.

So follow the instructions on building Qt from source,
except that you also provide the `-static` and `-bundled-xcb-xinput` options
for `configure`.
Then build the release executable with this Qt installation.

For a bundle that works on other machines,
you have to include certain Linux shared libraries.
But remember _not_ to include every dependency `ldd` lists,
as some of them would trump system-specific libraries.

[This bundle](https://csimmaviktor.web.elte.hu/calc_linux.zip)
seems to work.
Include these libraries and the start script with the executable
and you are ready to go.
Run `calc.sh` to start;
this helps the dynamic linker find the libraries attached.

### Windows

This is easier.

Build Qt as above and build the release executable with it.
After that, you only need two DLLs from the MinGW directory:
`libc++.dll` and `libunwind.dll`.
But if you use a different MinGW,
you can copy the executable into Windows Sandbox
and see what libraries it misses.

For a working example, see
[this bundle](https://csimmaviktor.web.elte.hu/calc_windows.zip).

