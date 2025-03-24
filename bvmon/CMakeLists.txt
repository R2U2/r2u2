cmake_minimum_required(VERSION 3.16)

project(bvmon LANGUAGES C CXX CUDA)

enable_language(CUDA)

set(CMAKE_POSITION_INDEPENDENT_CODE ON)

set(CMAKE_CUDA_ARCHITECTURES 50 52 60 61 70 72 75 80 86 87 89 90 100 101 120)
set(CMAKE_CUDA_FLAGS "${CMAKE_CUDA_FLAGS} -Wno-deprecated-gpu-targets")
if(CMAKE_BUILD_TYPE STREQUAL "Debug")
    set(CMAKE_CUDA_FLAGS "${CMAKE_CUDA_FLAGS} -G")  # enable cuda-gdb (expensive)
endif()

# Include directories and libraries
include_directories(../../../Common)

# Source file
# Add target for bvmon
add_executable(bvmon bvmon.cu)
# target_include_directories(bvmon SYSTEM PUBLIC /usr/local/cuda-12.8/targets/x86_64-linux/include/)

target_compile_options(bvmon PRIVATE $<$<COMPILE_LANGUAGE:CUDA>:--extended-lambda>)

set_target_properties(bvmon PROPERTIES CXX_STANDARD 17 CUDA_STANDARD 14)

set_target_properties(bvmon PROPERTIES CUDA_SEPARABLE_COMPILATION ON)
