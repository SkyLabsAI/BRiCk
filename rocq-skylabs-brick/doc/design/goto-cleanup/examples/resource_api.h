#ifndef GOTO_CLEANUP_RESOURCE_API_H
#define GOTO_CLEANUP_RESOURCE_API_H
#ifdef __cplusplus
extern "C" {
#endif
typedef int handle_t;
enum { somethnig = 21, somethnig_else = 22 };
handle_t getResource(void);
void freeResource(handle_t);
int action1(handle_t, handle_t);
int action2(handle_t, handle_t);
int somefunction(void);
#ifdef __cplusplus
}
#endif
#endif
