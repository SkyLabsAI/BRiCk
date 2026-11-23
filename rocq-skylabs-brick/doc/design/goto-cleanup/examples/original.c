// Source - https://stackoverflow.com/a/70446256
// Posted by KamilCuk, modified by community. See post Timeline for history.
// Retrieved 2026-11-23. This example is licensed CC BY-SA 4.0:
// https://creativecommons.org/licenses/by-sa/4.0/
// Adaptation by Codex: added the fixture header and explicit void parameter.
#include "resource_api.h"

int somefunction(void) {
    int errorcode = 0;

    handle_t res1 = getResource();
    if (!res1) {
        errorcode = somethnig;
        goto res1_fail;
    }
    handle_t res2 = getResource();
    if (!res2) {
        errorcode = somethnig_else;
        goto res2_fail;
    }

    errorcode = action1(res1, res2);
    if (!errorcode) {
       goto actions_fail;
    }
    errorcode = action2(res1, res2);
    if (!errorcode) {
       goto actions_fail;
    }

actions_fail:
    freeResource(res2);
res2_fail:
    freeResource(res1);
res1_fail:
    return errorcode;
}
