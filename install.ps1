# An installation script of the agda2hs SDK for Windows.
# Installs GHC, agda2hs, Ninja and CMake;
# then builds Qt from source with the necessary libraries and options.

# The original working directory (we'll switch here back in the end):
$ORIGINAL_PWD = $PWD

# GHCup
# Set-ExecutionPolicy Bypass -Scope Process -Force;[System.Net.ServicePointManager]::SecurityProtocol = [System.Net.ServicePointManager]::SecurityProtocol -bor 3072; try { & ([ScriptBlock]::Create((Invoke-WebRequest https://www.haskell.org/ghcup/sh/bootstrap-haskell.ps1 -UseBasicParsing))) -Interactive -DisableCurl } catch { Write-Error $_ }
# it starts the installation of GHC parallelised;
# so we include a prompt
Read-Host -Prompt "Please wait until GHC gets installed in the other window; then press Enter to continue"


# $NINJA_VERSION="1.12.1"
# $NINJA_URL="https://github.com/ninja-build/ninja/releases/download/v${NINJA_VERSION}/ninja-win.zip"
# $CMAKE_VERSION="3.30.5"
# $CMAKE_URL="https://github.com/Kitware/CMake/releases/download/v${CMAKE_VERSION}/cmake-${CMAKE_VERSION}-windows-x86_64.zip"
# $LLVM_VERSION="20220323"
# $LLVM_URL="https://github.com/mstorsjo/llvm-mingw/releases/download/${LLVM_VERSION}/llvm-mingw-${LLVM_VERSION}-ucrt-x86_64.zip"

# the Qt submodules to be installed
# $QT_SUBMODULES = @('qtbase', 'qtwayland', 'qtdoc', 'qttools')
$QT_VERSION="6.7.3"
# $QT_BASE_URL="https://download.qt.io/official_releases/qt/6.7/${QT_VERSION}"

# $QT_CREATOR_VERSION="14.0.2"
# $QT_CREATOR_URL="https://download.qt.io/official_releases/qtcreator/14.0/${QT_CREATOR_VERSION}/qt-creator-opensource-windows-x86_64-${QT_CREATOR_VERSION}.exe"

$is_done=$false
while (-not($is_done)) {
    $SDK_PATH = Read-Host -Prompt "Provide the path into which to install resources"

    if (-not(Test-Path "$SDK_PATH" -IsValid)) {
        Write-Error "Invalid path: $SDK_PATH. Try again."
    } elseif (Test-Path "$SDK_PATH" -PathType leaf) {
        Write-Error "Error: the given path points to a file"
    } else {
        # for folders, -Force does _not_ overwrite the existing one
        New-Item -Path "$SDK_PATH" -ItemType Directory -Force
        # conversion to absolute path
        $SDK_PATH = [System.IO.Path]::GetFullPath($SDK_PATH + '\')
        $is_done = $true
    }
}

cd "$SDK_PATH"
# git clone "https://github.com/viktorcsimma/agda2hs"
# cd agda2hs
# git checkout have-it-both-ways
# cabal install --overwrite-policy=always

# adding the agda2hs binary to PATH
[System.Environment]::SetEnvironmentVariable("Path", $env:Path + ";C:\cabal\bin", [System.EnvironmentVariableTarget]::User) # for later sessions, permanently
$env:Path += ";C:\cabal\bin" # for this session
# and for Clang, CMake and Ninja:
[System.Environment]::SetEnvironmentVariable("Path", $env:Path + "$SDK_PATH\Qt\Tools\llvm-mingw1706_64\bin;$SDK_PATH\Qt\Tools\CMake_64\bin;$SDK_PATH\Qt\Tools\Ninja", [System.EnvironmentVariableTarget]::User)
$env:Path += ";$SDK_PATH\Qt\Tools\llvm-mingw1706_64\bin;$SDK_PATH\Qt\Tools\CMake_64\bin;$SDK_PATH\Qt\Tools\Ninja"


# adding the agda2hs library to the Agda type checker
mkdir "$HOME\AppData\Roaming\agda"
Write-Output "$SDK_PATH\agda2hs\agda2hs.agda-lib"  | Out-File "$HOME\AppData\Roaming\agda\libraries" -Append -Encoding utf8



$TEMP_PATH=[System.IO.Path]::GetTempPath()
$ProgressPreference = 'SilentlyContinue' # this makes Invoke-WebRequest much faster by turning off the progress indicator

cd "$SDK_PATH"

# installing Qt via online installer
Write-Host "Downloading the Qt online installer..."
Invoke-WebRequest -Uri "https://d13lb3tujbc8s0.cloudfront.net/onlineinstallers/qt-online-installer-windows-x64-4.8.1.exe" -OutFile "$TEMP_PATH\installer.exe"
cd "$TEMP_PATH"
$version_without_dots = $QT_VERSION.split('.') -join ''   # the version number without dots
.\installer.exe --root "$SDK_PATH\Qt" --no-default-installations --accept-licenses install qt.qt6.${version_without_dots}.win64_llvm_mingw qt.tools.ninja qt.tools.cmake qt.tools.qtcreator_gui

Write-Host -Prompt "Please add C:\cabal\bin to PATH in order to access agda2hs."

# New-Item -Path "tools" -ItemType Directory -Force
# New-Item -Path "tools\bin" -ItemType Directory -Force

# installing Ninja

# Invoke-WebRequest -Uri "$NINJA_URL" -OutFile "$TEMP_PATH\ninja_win.zip"
# this only contains an exe; so it can go directly to bin:
# Expand-Archive -Path "$TEMP_PATH\ninja_win.zip" -DestinationPath "$SDK_PATH\tools\bin"

# installing CMake
# cd "$SDK_PATH/tools"
# Invoke-WebRequest -Uri "$CMAKE_URL" -OutFile "$TEMP_PATH\cmake.zip"
# Expand-Archive -Path "$TEMP_PATH\cmake.zip" -DestinationPath "$SDK_PATH\tools"
# Move-Item ".\tools\cmake-${CMAKE_VERSION}-windows-x86_64\" ".\tools\cmake"
# creating a symbolic link in tools\bin would require admin privileges... m'eh

# adding all those symlinks to PATH
# (beware: this is only for the current session!)
# $env:PATH="${env:PATH};${SDK_PATH}\tools\bin;${SDK_PATH}\tools\cmake\bin"

# installing the "correct" LLVM version for building
# a GHC-compatible Qt
# cd "$SDK_PATH"
# Invoke-WebRequest -Uri "$LLVM_URL" -OutFile "$TEMP_PATH\llvm-mingw.zip"
# Expand-Archive -Path "$TEMP_PATH\llvm-mingw.zip" -DestinationPath "$SDK_PATH\tools"
# Move-Item ".\tools\llvm-mingw-${LLVM_VERSION}-ucrt-x86_64\" ".\tools\llvm-mingw"

# installing Qt from source
# cd "$SDK_PATH"
# foreach ($submodule in $QT_SUBMODULES) {
#     Invoke-WebRequest -Uri "$QT_BASE_URL/submodules/${submodule}-everywhere-src-${QT_VERSION}.zip" -OutFile "$TEMP_PATH\${submodule}.zip"
#     Expand-Archive -Path "$TEMP_PATH\${submodule.zip}" -DestinationPath "$TEMP_PATH\qt-src"
# }
# Invoke-WebRequest -Uri "$QT_URL" -OutFile "$TEMP_PATH\qt.zip"
# Expand-Archive -Path "$TEMP_PATH\qt.zip" -DestinationPath "$TEMP_PATH\qt-src"

# finally:
cd "$ORIGINAL_PWD"
