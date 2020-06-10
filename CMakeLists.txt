cmake_minimum_required(VERSION 3.5)
project(RoundingSat2)

set(CMAKE_CXX_STANDARD 14)

if (NOT CMAKE_BUILD_TYPE)
    message(WARNING "Please use -DCMAKE_BUILD_TYPE=[build_type] where [build_type] is one of: Debug, Release, RelWithDebInfo and MinSizeRel")
endif()

set(build_static "ON"
    CACHE STRING "Build and use static libraries.")

set(profile_flags "OFF"
    CACHE STRING "Build using gprof flag (-pg).")

set(compilewithsoplex "OFF"
    CACHE STRING "Use SoPlex to check for rational infeasibility.")

set(soplex "${PROJECT_SOURCE_DIR}/soplex-5.0.0.tgz"
    CACHE STRING "SoPlex package, download at https://soplex.zib.de/download.php?fname=soplex-5.0.0.tgz")

set(testruns_timeout 1
    CACHE STRING "Timeout of individual test runs.")

IF(compilewithsoplex)
    # provides libsoplex and ${SOPLEX_INCLUDE_DIRS}
    include(${PROJECT_SOURCE_DIR}/cmake/soplex_build_and_load.cmake)
endif()

if(${build_static})
    set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} -static-libgcc -static-libstdc++ -static")
endif()

if(${profile_flags})
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -pg")
    set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} -pg")
    set(CMAKE_SHARED_LINKER_FLAGS "${CMAKE_SHARED_LINKER_FLAGS} -pg")
endif()

set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Wall -Wextra")

set(source_files
    src/aux.cpp
    src/Solver.cpp
    src/roundingsat.cpp
    src/quit.cpp
    src/LpSolver.cpp
    src/SolverStructs.cpp
)

set(header_files
    src/SolverStructs.hpp
    src/aux.hpp
    src/Logger.hpp
    src/Stats.hpp
    src/LpSolver.hpp
    src/Options.hpp
    src/IntSet.hpp
    src/Solver.hpp
    src/run.hpp
    src/typedefs.hpp
    src/globals.hpp
    src/SimpleCons.hpp
    src/parsing.hpp
    src/Constraint.hpp
    src/quit.hpp
)

set(all_files ${source_files} ${header_files})

add_executable(roundingsat ${source_files})
target_include_directories(roundingsat PRIVATE ${PROJECT_SOURCE_DIR}/src/ ${SOPLEX_INCLUDE_DIRS})

IF(compilewithsoplex)
    target_link_libraries(roundingsat libsoplex)
    target_compile_definitions(roundingsat PUBLIC WITHSOPLEX)
endif()

FIND_PROGRAM(CLANG_FORMAT "clang-format")
IF(CLANG_FORMAT)
    add_custom_target(
        format
        WORKING_DIRECTORY ${PROJECT_SOURCE_DIR}
        COMMAND ${CLANG_FORMAT}
        -style=file
        -i
        ${all_files}
    )
endif()

add_custom_target(
    testruns
    WORKING_DIRECTORY ${PROJECT_SOURCE_DIR}/test
    COMMAND ./run_tests.sh ${testruns_timeout} ${CMAKE_CURRENT_BINARY_DIR}/roundingsat
)
add_dependencies(testruns roundingsat)
