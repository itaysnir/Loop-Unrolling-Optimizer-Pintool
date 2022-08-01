Full name: Itay Snir

Compilation:
1. Extract the folder to: <pindir>/source/tools
2. run the following: make ex4.test


Run:
<pindir>/pin -t <pindir>/source/tools/ex4/obj-intel64/ex4.so -inst -- <binary>
OR
<pindir>/pin -t <pindir>/source/tools/ex4/obj-intel64/ex4.so -prof -- <binary>


Testing:
1. Run with "-dump" flag, and save to a local temporary file via "&> temp.txt" (this produces a huge file).
2. Look for occurrences of "[rbp-0x86c]", combined with a "cmp" instruction.
It should be the 12th occurrence of "[rbp-0x86c]".
3. Desired output:
The first 3 occurrences have an inverted jump criteria, jumping to the loop's unrolling end.
The final loop have the original jump criteria, and right after it - the loop's unrolling original end.
For example:

... (Loop body)
0x7f3d7a95b482: mov eax, dword ptr [rbp-0x18]
0x7f3d7a95b485: cmp eax, dword ptr [rbp-0x86c]
0x7f3d7a95b48b: jnl 0x7f3d7a95b683
0x7f3d7a95b491: mov eax, dword ptr [rbp-0x18]
0x7f3d7a95b494: sar eax, 0x5
... (Loop body)
0x7f3d7a95b528: mov eax, dword ptr [rbp-0x18]
0x7f3d7a95b52b: cmp eax, dword ptr [rbp-0x86c]
0x7f3d7a95b531: jnl 0x7f3d7a95b683
0x7f3d7a95b537: mov eax, dword ptr [rbp-0x18]
0x7f3d7a95b53a: sar eax, 0x5
... (Loop body)
0x7f3d7a95b5ce: mov eax, dword ptr [rbp-0x18]
0x7f3d7a95b5d1: cmp eax, dword ptr [rbp-0x86c]
0x7f3d7a95b5d7: jnl 0x7f3d7a95b683
0x7f3d7a95b5dd: mov eax, dword ptr [rbp-0x18]
0x7f3d7a95b5e0: sar eax, 0x5
... (Loop body)
0x7f3d7a95b674: mov eax, dword ptr [rbp-0x18]
0x7f3d7a95b677: cmp eax, dword ptr [rbp-0x86c]
0x7f3d7a95b67d: jl 0x7f3d7a95b3eb
0x7f3d7a95b683: mov dword ptr [rbp-0x2c], 0x0
0x7f3d7a95b68a: mov dword ptr [rbp-0x24], 0xffffffff
... (The code that resides right after the original loop)