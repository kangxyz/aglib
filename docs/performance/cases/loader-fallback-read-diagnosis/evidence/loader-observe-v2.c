#define _GNU_SOURCE
#include <dlfcn.h>
#include <errno.h>
#include <stdint.h>
#include <stddef.h>
#include <sys/mman.h>
#include <sys/syscall.h>
#include <unistd.h>
#include <string.h>
static void *(*real_mmap)(void *,size_t,int,int,int,off_t);
static void *(*real_mmap64)(void *,size_t,int,int,int,off64_t);
static ssize_t (*real_read)(int,void *,size_t);
static int enabled;
static unsigned records, mmap_nomem, mmap_exists, mmap_other, read_failures, read_shorts;
static char *word(char *p,const char *s){while(*s)*p++=*s++;return p;}
static char *number(char *p,unsigned long v){char b[32];unsigned n=0;do{b[n++]=(char)('0'+v%10);v/=10;}while(v);while(n)*p++=b[--n];return p;}
static char *signed_number(char *p,long v){if(v<0){*p++='-';return number(p,(unsigned long)(-(v+1))+1);}return number(p,(unsigned long)v);}
static void report(const char *kind,int fd,size_t count,long result,int error,int null_buffer){
 if(!enabled||__atomic_fetch_add(&records,1,__ATOMIC_RELAXED)>=64)return;
 char b[512],*p=b;p=word(p,"LEAN_LOADER_SYSCALL pid=");p=number(p,(unsigned long)syscall(SYS_getpid));p=word(p," op=");p=word(p,kind);p=word(p," fd=");p=signed_number(p,fd);p=word(p," requested=");p=number(p,count);p=word(p," result=");p=signed_number(p,result);p=word(p," errno=");p=signed_number(p,error);p=word(p," buffer_null=");p=number(p,(unsigned long)null_buffer);*p++='\n';(void)syscall(SYS_write,STDERR_FILENO,b,(size_t)(p-b));
}
__attribute__((constructor)) static void initialize(void){
 real_mmap=(void *(*)(void *,size_t,int,int,int,off_t))dlsym(RTLD_NEXT,"mmap");
 real_mmap64=(void *(*)(void *,size_t,int,int,int,off64_t))dlsym(RTLD_NEXT,"mmap64");
 real_read=(ssize_t (*)(int,void *,size_t))dlsym(RTLD_NEXT,"read");
 char path[4096];long n=syscall(SYS_readlink,"/proc/self/exe",path,sizeof(path)-1);
 if(n>0){path[n]=0;const char *name=strrchr(path,'/');name=name?name+1:path;enabled=strcmp(name,"axiom-audit")==0||strcmp(name,"loader-observe-control")==0;}
 if(enabled&&(!real_mmap||!real_read)){const char m[]="LEAN_LOADER_OBSERVER_RESOLUTION_FAILED\n";(void)syscall(SYS_write,2,m,sizeof(m)-1);_exit(125);}
}
void *mmap(void *a,size_t n,int prot,int flags,int fd,off_t off){
 void *r=real_mmap?real_mmap(a,n,prot,flags,fd,off):(void *)syscall(SYS_mmap,a,n,prot,flags,fd,off);int e=errno;
 if(r==MAP_FAILED){if(e==ENOMEM){if(__atomic_fetch_add(&mmap_nomem,1,__ATOMIC_RELAXED)<4)report("mmap",fd,n,-1,e,a==NULL);}else if(e==EEXIST){__atomic_fetch_add(&mmap_exists,1,__ATOMIC_RELAXED);}else if(__atomic_fetch_add(&mmap_other,1,__ATOMIC_RELAXED)<4){report("mmap",fd,n,-1,e,a==NULL);}}
 errno=e;return r;
}
void *mmap64(void *a,size_t n,int prot,int flags,int fd,off64_t off){
 void *r=real_mmap64?real_mmap64(a,n,prot,flags,fd,off):(void *)syscall(SYS_mmap,a,n,prot,flags,fd,off);int e=errno;
 if(r==MAP_FAILED){if(e==ENOMEM){if(__atomic_fetch_add(&mmap_nomem,1,__ATOMIC_RELAXED)<4)report("mmap64",fd,n,-1,e,a==NULL);}else if(e==EEXIST){__atomic_fetch_add(&mmap_exists,1,__ATOMIC_RELAXED);}else if(__atomic_fetch_add(&mmap_other,1,__ATOMIC_RELAXED)<4){report("mmap64",fd,n,-1,e,a==NULL);}}
 errno=e;return r;
}
ssize_t read(int fd,void *b,size_t n){
 ssize_t r=real_read?real_read(fd,b,n):(ssize_t)syscall(SYS_read,fd,b,n);int e=errno;
 if(r<0){if(__atomic_fetch_add(&read_failures,1,__ATOMIC_RELAXED)<16)report("read",fd,n,(long)r,e,b==NULL);}else if(n>0&&(size_t)r<n){if(__atomic_fetch_add(&read_shorts,1,__ATOMIC_RELAXED)<4)report("read_short",fd,n,(long)r,0,b==NULL);}
 errno=e;return r;
}

__attribute__((destructor)) static void summarize(void){report("count_mmap_ENOMEM",-1,mmap_nomem,0,0,0);report("count_mmap_EEXIST",-1,mmap_exists,0,0,0);report("count_mmap_other",-1,mmap_other,0,0,0);report("count_read_failure",-1,read_failures,0,0,0);report("count_read_short",-1,read_shorts,0,0,0);}
