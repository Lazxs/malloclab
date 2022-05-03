## Do implementations in stages ##
+ mm_ver0.c----根据csapp textbook 9.9.12完善一个最简单的隐式+首次匹配

+ mm_ver1.c----显式空闲链表

+ mm_ver1.5.c--最佳适配

+ mm_ver1.6.c--分离空闲链表测试

+ mm_ver2.c----分离空闲链表+最佳匹配+独立realloc

在做的过程中遇到了很多segmentation fault，gcc -g用cgdb调试会更方便；

malloclab.pdf中的HINTS很有帮助。
