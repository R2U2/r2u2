################################################################################
# Automatically-generated file. Do not edit!
################################################################################

# Add inputs and outputs from these tool invocations to the build variables 
CPP_SRCS += \
../src/Assembly.cpp \
../src/CircularBuffer.cpp \
../src/Formula.cpp \
../src/MTL.cpp \
../src/Observer.cpp 

OBJS += \
./src/Assembly.o \
./src/CircularBuffer.o \
./src/Formula.o \
./src/MTL.o \
./src/Observer.o 

CPP_DEPS += \
./src/Assembly.d \
./src/CircularBuffer.d \
./src/Formula.d \
./src/MTL.d \
./src/Observer.d 


# Each subdirectory must supply rules for building sources it contributes
src/%.o: ../src/%.cpp
	@echo 'Building file: $<'
	@echo 'Invoking: GCC C++ Compiler'
	g++ -O0 -g3 -Wall -c -fmessage-length=0 -std=c++11 -MMD -MP -MF"$(@:%.o=%.d)" -MT"$(@)" -o "$@" "$<"
	@echo 'Finished building: $<'
	@echo ' '


