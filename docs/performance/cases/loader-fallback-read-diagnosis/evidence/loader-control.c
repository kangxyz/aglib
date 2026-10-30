#define _GNU_SOURCE
#include <sys/mman.h>
#include <stdint.h>
#include <unistd.h>
int main(void){void *p=mmap(0,SIZE_MAX,PROT_READ,MAP_PRIVATE|MAP_ANONYMOUS,-1,0);ssize_t r=read(-1,0,1);return p==MAP_FAILED && r==-1 ? 0:1;}
