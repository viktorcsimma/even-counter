#!/bin/sh

# An installation script of the agda2hs SDK for Ubuntu/Debian.
# Tested on Ubuntu 24.04.
# Installs GHC, agda2hs, Ninja and CMake;
# then builds Qt from source with the necessary libraries and options.

# NOTE: for me, this was needed for Qt:
# sudo apt update
# sudo apt upgrade
# sudo apt install libclang-17-dev
# but then on Ubuntu 24.04, it was libclang-18-dev... huh

NINJA_VERSION=1.12.1
NINJA_URL="https://github.com/ninja-build/ninja/releases/download/v${NINJA_VERSION}/ninja-linux.zip"
CMAKE_VERSION=3.30.3
CMAKE_URL="https://github.com/Kitware/CMake/releases/download/v${CMAKE_VERSION}/cmake-${CMAKE_VERSION}-linux-x86_64.sh"
QT_VERSION=6.7.2
QT_URL="https://download.qt.io/official_releases/qt/6.7/${QT_VERSION}/single/qt-everywhere-src-${QT_VERSION}.tar.xz"
QT_CREATOR_VERSION=14.0.1
QT_CREATOR_URL="https://download.qt.io/official_releases/qtcreator/14.0/${QT_CREATOR_VERSION}/qt-creator-opensource-linux-x86_64-${QT_CREATOR_VERSION}.run"

is_done=1  # false
while [ 0 -ne "$is_done" ]; do
    echo -n "Provide the path into which to install resources: "
    read SDK_PATH

    # if [ ( ! "$SDK_PATH" ) -o ( "$SDK_PATH" == " " ) ]; then
    #     SDK_PATH="~"
    # fi

    # converting relative paths to absolute ones
    if [ '~' = `echo "$SDK_PATH" | cut -c 1` ]; then
        SDK_PATH="$HOME/`echo "$SDK_PATH" | cut -c 2-`"
    elif [ '/' != `echo "$SDK_PATH" | cut -c 1` ]; then
	SDK_PATH="$PWD/$SDK_PATH"
    fi
 
    if [ -f "$SDK_PATH" ]; then
	echo "Error: the given path points to a file" >&2
    elif [ ! -d "$SDK_PATH" ]; then
	if mkdir "$SDK_PATH"; then
	    is_done=0
	else
	    echo "Error when creating directory \"$SDK_PATH\"" >&2
	fi
    else
	is_done=0
    fi
done

cd "$SDK_PATH"

# installing GHC
curl --proto '=https' --tlsv1.2 -sSf https://get-ghcup.haskell.org | sh

# installing agda2hs
git clone https://github.com/viktorcsimma/agda2hs
cd agda2hs
git checkout have-it-both-ways
~/.ghcup/bin/cabal install

# installing Ninja
cd "$SDK_PATH"
mkdir tools; mkdir tools/bin
curl -L "$NINJA_URL" > /tmp/ninja.zip
unzip /tmp/ninja.zip -d "$SDK_PATH/tools/ninja"
# this creates a binary called "ninja" in "$SDK_PATH/tools/ninja"
cd "$SDK_PATH/tools/bin"
ln -s "$SDK_PATH/tools/ninja/ninja"
rm /tmp/ninja.zip

# installing CMake
cd "$SDK_PATH/tools"
curl -L "$CMAKE_URL" > /tmp/cmake.sh
yes | sh /tmp/cmake.sh
rm /tmp/cmake.sh
# creating symlinks in tools/bin
cd "${SDK_PATH}/tools/cmake-${CMAKE_VERSION}-linux-x86_64/bin/"
for filename in *; do
    ln -s "$PWD/$filename" "${SDK_PATH}/tools/bin/$filename"
done

# adding all those symlinks to PATH
# (beware: this is only for the current session!)
export PATH="$PATH:${SDK_PATH}/tools/bin"

# installing Qt from source
# /tmp has a limited capacity;
# so we do this under $SDK_PATH
cd "$SDK_PATH"
# -L is for following redirects
curl -L "$QT_URL" > qt.tar.xz
tar -xvf qt.tar.xz
cd "$SDK_PATH/tools"
mkdir qt-build; cd qt-build
"$SDK_PATH/qt-everywhere-src-${QT_VERSION}/configure" -static -bundled-xcb-xinput -skip qtquick3d -skip qt3d -skip qtcharts -skip qtdatavis3d -skip qtgraphs -skip qtwebsockets -skip qthttpserver -skip qtserialport -skip qtpositioning -skip qtlocation -skip qtwebchannel -skip qtwebengine -skip qtnetworkauth -skip qtquick3dphysics -skip qtremoteobjects -skip qtsensors -skip qtserialbus -skip qtspeech -skip qtwebview
cmake --build . --parallel
sudo cmake --install . # I could not manage without it – what about the -prefix option when configuring?  

# installing Qt Creator through a binary installer
curl -L "$QT_CREATOR_URL" > /tmp/qt_creator.run
chmod u+x /tmp/qt_creator.run
/tmp/qt_creator.run
# I also needed sudo apt install libxcb-cursor0 for this to work

# here, I could only add the Qt installation through the GUI

