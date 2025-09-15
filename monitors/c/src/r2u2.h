#ifndef R2U2_H
#define R2U2_H

#include "internals/errors.h"
#include "memory/monitor.h"

/// @brief      Get a default monitor from spec file
/// @param[in]  spec  Pointer to binary spec file
/// @param[in]  status  Indicates status of getting monitor
/// @return     r2u2_monitor_t The configured monitor
r2u2_monitor_t r2u2_get_monitor(uint8_t* spec, r2u2_status_t *status);

/// @brief      Get a default monitor from spec file
/// @param[in]  spec  Pointer to binary spec file
/// @param[in]  monitor  Pointer to r2u2_monitor_t
/// @return     r2u2_status_t
r2u2_status_t r2u2_update_binary_file(uint8_t* spec, r2u2_monitor_t *monitor);

/// @brief      Take a step with runtime monitor
/// @param[in]  monitor  Pointer to (configured) R2U2 monitor
/// @return     r2u2_status_t
r2u2_status_t r2u2_monitor_step(r2u2_monitor_t *monitor);


#endif
