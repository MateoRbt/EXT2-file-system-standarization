------------------------------- MODULE inode -------------------------------
EXTENDS Integers,TLC,Sequences,FiniteSets
CONSTANTS InodeCount, BlockCount,N,blockSize


Inode ==  [
                iNum    |-> 0, (* Inode number is equal to its index in the array *)
                mode    |-> "none", (* File type and permission bits *)
                uid      |-> 0, (* User ID of the file's owner *)
                size     |-> 0, (* File size in bytes, initially set to 1024 bytes *)
                atime    |-> 0, (* Last time the file was accessed *)
                ctime    |-> 0, (* Last time the file was changed *)
                mtime    |-> 0, (* Last time the file was modified *)
                dtime    |-> 0, (* Last time the file was deleted *)
                gid     |-> 0, (* Group ID of the file's owner *)
                links_count  |-> 0, (* Number of hard links to the file *)
                blocks   |-> 0, (* Number of blocks used by the file *)
                flags    |-> 0, (* File flags *)
                osd1     |-> 0, (* Operating system dependent field *)
                directAddr  |-> [b \in 0..11 |-> -1],  (* Direct block addresses,
                 initialized with -1 indicating that it's not pointing to any block *)
                generation  |-> 0, (* File version (used for NFS) *)
                file_acl    |-> -1, (* File access control list *)
                dir_acl     |-> -1 (* Directory*) 
            ]




(* superblock data structure *)
sb == [
        inodes_count   |-> InodeCount,  (* total number of inodes *)
        blocks_count   |-> BlockCount,  (* total number of blocks *)
        r_blocks_count |-> 0,           (* number of reserved blocks *)
        free_blocks_count |-> BlockCount, (* number of free blocks *)
        free_inodes_count |-> InodeCount, (* number of free inodes *)
        first_data_block |-> 0,         (* number of the first data block *)
        log_block_size  |-> blockSize,          (* block size = 1024 << log_block_size *)
        log_frag_size   |-> 1024,          (* fragment size = 1024 << log_frag_size *)
        blocks_per_group|-> BlockCount \div N,          (* number of blocks per block group *)
        inodes_per_group|-> InodeCount \div N,          (* number of inodes per block group *)
        first_ino       |-> 11,         (* In revision 0, the first non-reserved inode is fixed to 11 *)
        inode_size      |-> 128,        (*  value indicating the size of the inode structure *)
        block_group_nr  |-> 1          (* ndicate the block group number hosting this superblock structure *)
       ]
       

dir_entry == [
               inode |-> 0, (* inode number associated with the file*)
               rec_len |-> 0, (*length of the record*)
               name_len |-> 0, (*length of filename*)
               filename |-> "" (*name of the file*)
             ]
 
BGD_entry == [
                bg_block_bitmap |-> 0,(*the firts free data block in the block bitmap*)
                bg_inode_bitmap |-> 0, (*the first free inode in the inode bitmap*)
                bg_inode_table |-> 0 , (*the first free inode in the inode table*)
                bg_free_block_count |-> sb.blocks_per_group, (*the count of the free blocks*)
                bg_free_inode_count |-> sb.inodes_per_group, (*the count of the free inodes*)
                bg_used_dir_count |-> 1, (*the count of used directories *)
                bg_pad |-> 0, (*used for padding the structure on a 32bit boundary*)
                bg_reserved |-> 10 (*reserved for future purpose*) 
             ]
             
BlockGroupDescriptorTable ==  [i \in 0..N-1 |-> BGD_entry]      
       
(* Invariants *)
InodeCountInvariant == sb.inodes_count = InodeCount
BlockCountInvariant == sb.blocks_count = BlockCount
FreeBlockCountInvariant == sb.free_blocks_count <= BlockCount
FreeInodeCountInvariant == sb.free_inodes_count <= InodeCount


=============================================================================
\* Modification History
\* Last modified Sat May 06 18:38:10 EEST 2023 by mateo
\* Created Wed Jan 11 22:28:26 EET 2023 by mateo
