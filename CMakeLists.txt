cmake_minimum_required(VERSION 2.6 FATAL_ERROR)

project(glucose)
set(CMAKE_RUNTIME_OUTPUT_DIRECTORY "${CMAKE_CURRENT_SOURCE_DIR}/simp")
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -std=c++11 -Wno-parentheses -Wall -O3 -Wno-unused-label")

#--------------------------------------------------------------------------------------------------
# Configurable options:

option(STATIC_BINARIES "Link binaries statically." ON)
option(USE_SORELEASE "Use SORELEASE in shared library filename." ON)

#--------------------------------------------------------------------------------------------------
# Library version:

set(GLUCOSE_SOMAJOR 5)
set(GLUCOSE_SOMINOR 0)
set(GLUCOSE_SORELEASE 0)

# Compute VERSION and SOVERSION:
if (USE_SORELEASE)
    set(GLUCOSE_VERSION ${GLUCOSE_SOMAJOR}.${GLUCOSE_SOMINOR}.${GLUCOSE_SORELEASE})
else ()
    set(GLUCOSE_VERSION ${GLUCOSE_SOMAJOR}.${GLUCOSE_SOMINOR})
endif ()
set(GLUCOSE_SOVERSION ${GLUCOSE_SOMAJOR})

#--------------------------------------------------------------------------------------------------
# Dependencies:

find_package(ZLIB)
include_directories(${ZLIB_INCLUDE_DIR})
include_directories(${glucose_SOURCE_DIR})
#--------------------------------------------------------------------------------------------------
# Compile flags:

add_definitions(-D__STDC_FORMAT_MACROS -D__STDC_LIMIT_MACROS)

#--------------------------------------------------------------------------------------------------
# Build Targets:


set(GLUCOSE_LIB_SOURCES
        utils/Options.cc
        utils/System.cc
        core/Solver.cc
        core/Restart.cc
        core/lcm.cc
        core/ClauseManager.cc
        core/CCANR.cc
        simp/SimpSolver.cc
        parallel/ParallelSolver.cc
        )

link_directories(${CMAKE_CURRENT_SOURCE_DIR}/pfactory/lib)


add_library(glucose-lib-static STATIC ${GLUCOSE_LIB_SOURCES})
#add_library(glucose-lib-shared SHARED ${GLUCOSE_LIB_SOURCES})

#target_link_libraries(glucose-lib-shared ${ZLIB_LIBRARY})
target_link_libraries(glucose-lib-static ${ZLIB_LIBRARY})

#target_link_libraries(glucose-lib-shared pthread)
target_link_libraries(glucose-lib-static pthread)

#target_link_libraries(glucose-lib-shared pFactory)
target_link_libraries(glucose-lib-static pFactory)


add_executable(glucose simp/Main.cc)

if (STATIC_BINARIES)
    target_link_libraries(glucose glucose-lib-static)
else ()
    target_link_libraries(glucose glucose-lib-shared)
endif ()

set_target_properties(glucose-lib-static PROPERTIES OUTPUT_NAME "glucose")
#set_target_properties(glucose-lib-shared
#        PROPERTIES
#        OUTPUT_NAME "glucose"
#        VERSION ${GLUCOSE_VERSION}
#        SOVERSION ${GLUCOSE_SOVERSION})


#--------------------------------------------------------------------------------------------------
# Installation targets:

install(TARGETS glucose-lib-static glucose
        RUNTIME DESTINATION bin
        LIBRARY DESTINATION lib
        ARCHIVE DESTINATION lib)

install(DIRECTORY mtl utils core simp
        DESTINATION include/glucose
        FILES_MATCHING PATTERN "*.h")