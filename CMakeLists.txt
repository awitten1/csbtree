cmake_minimum_required(VERSION 3.24)

project(csb LANGUAGES CXX)

set(CMAKE_EXPORT_COMPILE_COMMANDS ON)
set(CMAKE_CXX_STANDARD 11)
add_library(csb csb.cc)
target_include_directories(csb PUBLIC ${CMAKE_CURRENT_LIST_DIR})
