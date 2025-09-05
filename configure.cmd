:<<"::CMDGOTO"
@echo off
goto :CMDENTRY
rem https://stackoverflow.com/questions/17510688/single-script-to-run-in-both-windows-batch-and-linux-bash
::CMDGOTO

echo "========== 3o3 build ${SHELL} ================="
DIR=$(dirname "$0")
(mkdir -p ${DIR}/build;)
(cd ${DIR}/build;cc ../tools/build.c -o build.exe)
(cd ${DIR}/build;./build.exe $1 $2)
exit $?
:CMDENTRY

echo ============= 3o3 build %COMSPEC% ============
set OLDDIR=%CD%

mkdir build  >nul 2>&1
chdir /d build
if "%CD%" == "%OLDDIR%" (
	echo dont build in source tree! 
	exit 1
)
cl %~dp0\tools\build.c /D_CRT_SECURE_NO_WARNINGS=1 /Fe:build.exe >>build.log 2>&1
clang -D_CRT_SECURE_NO_WARNINGS=1 %~dp0\tools\build.c -o build.exe >>build.log 2>&1
echo build %1 %2
.\build.exe %1 %2
chdir /d %OLDDIR%
exit 0


