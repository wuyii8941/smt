@echo off
setlocal enabledelayedexpansion

:: 设置输入目录和输出目录
set "INPUT_DIR=cases"
set "OUTPUT_DIR=output"

:: 确保输出目录存在
if not exist "%OUTPUT_DIR%" mkdir "%OUTPUT_DIR%"

:: 遍历 INPUT_DIR 目录下的所有 .smt 文件
for %%f in (%INPUT_DIR%\*.smt) do (
    set "filename=%%~nxf"
    echo Processing: %%f -> %OUTPUT_DIR%\!filename!
    cargo run -- "%%f" "%OUTPUT_DIR%\!filename!"
)

echo All files processed.
