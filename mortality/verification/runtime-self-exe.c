#define _GNU_SOURCE
#include <unistd.h>
#include <dlfcn.h>
#include <stdio.h>
#include <string.h>

/* This runtime exposes /proc/self/exe but not /proc/<getpid()>/exe.
   Preserve readlink semantics and redirect only that process's own exe path. */
ssize_t readlink(const char *path, char *buf, size_t size) {
    ssize_t (*original)(const char *, char *, size_t) = dlsym(RTLD_NEXT, "readlink");
    char own[64];
    snprintf(own, sizeof own, "/proc/%d/exe", (int)getpid());
    return original(strcmp(path, own) == 0 ? "/proc/self/exe" : path, buf, size);
}

