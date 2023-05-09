cmake_minimum_required(VERSION 2.6)

project(glucose)

option(BUILD_SHARED_LIBS OFF "True for building shared object")

set(CMAKE_CXX_FLAGS "-std=c++11")

# Dependencies {{{
find_package(ZLIB REQUIRED)
find_package(Threads REQUIRED)
# }}}

set(main_simp "simp/Main.cc")
set(main_parallel "parallel/Main.cc")

# Basic Library
file(GLOB lib_srcs RELATIVE ${CMAKE_CURRENT_SOURCE_DIR} mtl/*.cc core/*.cc simp/*.cc utils/*.cc)
list(REMOVE_ITEM lib_srcs ${main_simp} ${main_parallel})

message(${lib_srcs})

# Parallel Library
file(GLOB lib_parallel_srcs RELATIVE ${CMAKE_CURRENT_SOURCE_DIR} parallel/*.cc)
list(REMOVE_ITEM lib_parallel_srcs ${main_simp} ${main_parallel})


if(BUILD_SHARED_LIBS)
    set(lib_type "SHARED")
else()
    set(lib_type "STATIC")
endif()


include_directories(
        ${CMAKE_CURRENT_SOURCE_DIR}
        ${ZLIB_INCLUDE_DIR})

link_libraries(${ZLIB_LIBRARY})

# base library
add_library(glucose ${lib_type} ${lib_srcs})

add_executable(glucose-simp ${main_simp})
target_link_libraries(glucose-simp glucose)

# PARALLEL STUFF:
add_library(glucosep ${lib_type} ${lib_srcs} ${lib_parallel_srcs})
add_executable(glucose-syrup ${main_parallel})
target_link_libraries(glucose-syrup glucosep ${CMAKE_THREAD_LIBS_INIT})