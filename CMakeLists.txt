cmake_minimum_required(VERSION 3.5)
project(RoundingSat2)

set(CMAKE_CXX_STANDARD 14)

set(CMAKE_MODULE_PATH "${PROJECT_SOURCE_DIR}/cmake/")

#find_package(ZLIB REQUIRED)

# uncomment to profile with gprof
#SET(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -pg")
#SET(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} -pg")
#SET(CMAKE_SHARED_LINKER_FLAGS "${CMAKE_SHARED_LINKER_FLAGS} -pg")

# uncomment to do something ugly
#SET(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Ofast")

SET(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Wall -Wextra")

add_executable(roundingsat src/roundingsat.cpp)
#target_link_libraries(roundingsat ${CMAKE_SOURCE_DIR}/lib/libsoplex.a z)
#target_include_directories(roundingsat PRIVATE "${CMAKE_SOURCE_DIR}/lib")

ADD_CUSTOM_TARGET(release
  COMMAND ${CMAKE_COMMAND} -DCMAKE_BUILD_TYPE=Release ${CMAKE_SOURCE_DIR}
  COMMAND ${CMAKE_COMMAND} --build ${CMAKE_BINARY_DIR} --target roundingsat
  COMMENT "Creating executable in release mode.")

add_executable(roundingsat_info src/roundingsat.cpp)
#target_link_libraries(roundingsat_info ${CMAKE_SOURCE_DIR}/lib/libsoplex.a z)
#target_include_directories(roundingsat_info PRIVATE "${CMAKE_SOURCE_DIR}/lib")

ADD_CUSTOM_TARGET(info
  COMMAND ${CMAKE_COMMAND} -DCMAKE_BUILD_TYPE=RelWithDebInfo ${CMAKE_SOURCE_DIR}
  COMMAND ${CMAKE_COMMAND} --build ${CMAKE_BINARY_DIR} --target roundingsat_info
  COMMENT "Creating executable in release mode with debug info.")

add_executable(roundingsat_debug src/roundingsat.cpp)
#target_link_libraries(roundingsat_debug ${CMAKE_SOURCE_DIR}/lib/libsoplex_debug.a z)
#target_include_directories(roundingsat_debug PRIVATE "${CMAKE_SOURCE_DIR}/lib")

ADD_CUSTOM_TARGET(debug
  COMMAND ${CMAKE_COMMAND} -DCMAKE_BUILD_TYPE=Debug ${CMAKE_SOURCE_DIR}
  COMMAND ${CMAKE_COMMAND} --build ${CMAKE_BINARY_DIR} --target roundingsat_debug
  COMMENT "Creating executable in debug mode.")
