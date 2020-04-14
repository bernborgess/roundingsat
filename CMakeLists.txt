cmake_minimum_required(VERSION 3.5)
project(RoundingSat2)

set(CMAKE_CXX_STANDARD 14)
set(CMAKE_MODULE_PATH "${PROJECT_SOURCE_DIR}/cmake/")
find_package(ZLIB REQUIRED)

file(GLOB ALL_CPP_FILES ${PROJECT_SOURCE_DIR}/src/*.cpp)
file(GLOB ALL_HPP_FILES ${PROJECT_SOURCE_DIR}/src/*.hpp)
file(GLOB ALL_SRC_FILES ${PROJECT_SOURCE_DIR}/src/*.cpp ${PROJECT_SOURCE_DIR}/src/*.hpp)

# uncomment to profile with gprof
#set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -pg")
#set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} -pg")
#set(CMAKE_SHARED_LINKER_FLAGS "${CMAKE_SHARED_LINKER_FLAGS} -pg")

# uncomment to do something ugly
#set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Ofast")

set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Wall -Wextra")

add_executable(roundingsat ${ALL_CPP_FILES})
target_link_libraries(roundingsat ${CMAKE_SOURCE_DIR}/src/soplex/libsoplex.a z)
target_include_directories(roundingsat PRIVATE "${CMAKE_SOURCE_DIR}/src/soplex")

add_custom_target(release
  COMMAND ${CMAKE_COMMAND} -DCMAKE_BUILD_TYPE=Release ${CMAKE_SOURCE_DIR}
  COMMAND ${CMAKE_COMMAND} --build ${CMAKE_BINARY_DIR} --target roundingsat -j4
  COMMENT "Creating executable in release mode.")

add_custom_target(release_single
  COMMAND ${CMAKE_COMMAND} -DCMAKE_BUILD_TYPE=Release ${CMAKE_SOURCE_DIR}
  COMMAND ${CMAKE_COMMAND} --build ${CMAKE_BINARY_DIR} --target roundingsat
  COMMENT "Creating executable in release mode.")

add_executable(roundingsat_debug ${ALL_CPP_FILES})
target_link_libraries(roundingsat_debug ${CMAKE_SOURCE_DIR}/src/soplex/libsoplex_debug.a z)
target_include_directories(roundingsat_debug PRIVATE "${CMAKE_SOURCE_DIR}/src/soplex")

add_custom_target(debug
  COMMAND ${CMAKE_COMMAND} -DCMAKE_BUILD_TYPE=Debug ${CMAKE_SOURCE_DIR}
  COMMAND ${CMAKE_COMMAND} --build ${CMAKE_BINARY_DIR} --target roundingsat_debug -j4
  COMMENT "Creating executable in debug mode.")

add_custom_target(debug_single
  COMMAND ${CMAKE_COMMAND} -DCMAKE_BUILD_TYPE=Debug ${CMAKE_SOURCE_DIR}
  COMMAND ${CMAKE_COMMAND} --build ${CMAKE_BINARY_DIR} --target roundingsat_debug
  COMMENT "Creating executable in debug mode.")

add_executable(roundingsat_info ${ALL_CPP_FILES})
target_link_libraries(roundingsat_info ${CMAKE_SOURCE_DIR}/src/soplex/libsoplex.a z)
target_include_directories(roundingsat_info PRIVATE "${CMAKE_SOURCE_DIR}/src/soplex")

add_custom_target(info
        COMMAND ${CMAKE_COMMAND} -DCMAKE_BUILD_TYPE=RelWithDebInfo ${CMAKE_SOURCE_DIR}
        COMMAND ${CMAKE_COMMAND} --build ${CMAKE_BINARY_DIR} --target roundingsat_info -j4
        COMMENT "Creating executable in release mode with debug info.")

add_custom_target(
        format
        COMMAND /usr/bin/clang-format
        -style=file
        -i
        ${ALL_SRC_FILES}
)
