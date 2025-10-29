#ifndef R2U2_H
#define R2U2_H

#include "internals/errors.h"
#include "memory/monitor.h"

/// @brief      Update monitor with new spec file
/// @param[in]  spec  Pointer to binary spec file
/// @param[in]  monitor  Pointer to (configured) R2U2 monitor
/// @return     r2u2_status_t
r2u2_status_t r2u2_load_specification(uint8_t* spec, r2u2_monitor_t* monitor);

/// @brief      Take a step with runtime monitor
/// @param[in]  monitor  Pointer to (configured) R2U2 monitor
/// @return     r2u2_status_t
r2u2_status_t r2u2_monitor_step(r2u2_monitor_t* monitor);

/// @brief      Load a boolean value into R2U2
/// @param[in]  monitor  Pointer to (configured) R2U2 monitor
/// @param[in]  index  Mapping index into R2U2 (configured in CSV trace header or map file
///                    when specifications were compiled in C2PO)
/// @param[in]  value  Boolean value of type r2u2_bool to load
void r2u2_load_bool_value(r2u2_monitor_t* monitor, size_t index, r2u2_bool value);

/// @brief      Load an integer value into R2U2
/// @param[in]  monitor  Pointer to (configured) R2U2 monitor
/// @param[in]  index  Mapping index into R2U2 (configured in CSV trace header or map file
///                    when specifications were compiled in C2PO)
/// @param[in]  value  Integer value of type r2u2_int to load
void r2u2_load_int_value(r2u2_monitor_t* monitor, size_t index, r2u2_int value);

/// @brief      Load a float value into R2U2
/// @param[in]  monitor  Pointer to (configured) R2U2 monitor
/// @param[in]  index  Mapping index into R2U2 (configured in CSV trace header or map file
///                    when specifications were compiled in C2PO)
/// @param[in]  value  Float value of type r2u2_float to load
void r2u2_load_float_value(r2u2_monitor_t* monitor, size_t index, r2u2_float value);

/// @brief      Load a string value into R2U2
/// @param[in]  monitor  Pointer to (configured) R2U2 monitor
/// @param[in]  index  Mapping index into R2U2 (configured in CSV trace header or map file
///                    when specifications were compiled in C2PO)
/// @param[in]  value  String value to load. String will get parsed as float if decimal point 
///                   is found; otherwise will be parsed as boolean/integer
void r2u2_load_string_value(r2u2_monitor_t* monitor, size_t index, char* value);

#endif
