---------------------------- MODULE FileCreation ----------------------------
EXTENDS Integers,TLC,Sequences,FiniteSets,inode

(* --algorithm Createfile
  
variables
    inodeBitmap = [i \in 0..sb.inodes_per_group-1 |-> "FREE"] , 
    (* inode bitmap, with each bit representing the allocation status of an inode *)
    blockBitmap = [i \in 0..sb.blocks_per_group-1 |-> "FREE"],
    block_num = -1,
    bl = 0,
    in = 0,
    FreeInodeCount = {i \in 0..sb.inodes_per_group-1 : inodeBitmap[i] = "FREE"}, 
    FreeBlockCount = {i \in 0..sb.blocks_per_group-1 : blockBitmap[i] = "FREE"}, 
    InodeTable = [i \in 0..sb.inodes_per_group-1|->Inode] ,
    de = dir_entry,
    lenlist = 0,
    dirlist = << >> ,
    BGDT=BlockGroupDescriptorTable,
    sbins=sb,
    inode_num = -1;
    
define
FreeInodeExistsInvariant == \E i \in 0..sb.inodes_per_group-1 : inodeBitmap[i] = "FREE"
InodeInRange == de.inode \in 0..InodeCount-1
BlockNum == \E i \in 0..sb.inodes_per_group-1 : (InodeTable[i].blocks > 0 => \A j \in
0..InodeTable[i].blocks: InodeTable[i].directAddr[j] \in 0..sb.blocks_per_group-1)
FreeInodeCountProp == \A i \in FreeInodeCount: inodeBitmap[i] = "FREE"
FreeBlockCountProp == \A i \in FreeBlockCount: blockBitmap[i] = "FREE"
ValidRecLen == \A i \in 1..lenlist :dirlist[i].rec_len > 0
ValidNameLen == \A i \in 1..lenlist : dirlist[i].name_len >0 
ValidFilename == \A i \in 1..lenlist : dirlist[i].filename # "" 
max_file_size == \A i \in 0..sb.inodes_per_group-1 : InodeTable[i].size <= sb.blocks_per_group * sb.log_block_size
AllInodesCovered == [](\A i \in 0..sb.inodes_per_group-1 : inodeBitmap[i]\in {"FREE","ALLOCATED"})
AllblocksCovered == [](\A i \in 0..sb.blocks_per_group-1 : blockBitmap[i]\in {"FREE","ALLOCATED"})
ValidMode == [](\A i \in 0..sb.inodes_per_group-1 : InodeTable[i].mode \in {"ext2_reg", "ext2_dir", "ext2_symlink","none"})
InodeAllocation == [](\A i \in 0..sb.inodes_per_group-1 : InodeTable[i].dtime \in {0, -1})
end define;   

procedure FindFreeInode () begin
 find:
  while in < sb.inodes_per_group do
    if (inodeBitmap[in] = "FREE") then 
        inodeBitmap[in] := "ALLOCATED";
        inode_num := in;
        FreeInodeCount := FreeInodeCount \ {in};
        goto final;
    else
        in:=in+1;
    end if;
  end while;
final: return ;
end procedure;

procedure FindFreeBlock () begin
 find:
  while bl < sb.blocks_per_group do
    if (blockBitmap[bl] = "FREE") then 
        blockBitmap[bl] := "ALLOCATED";
        block_num := bl;
        FreeBlockCount := FreeBlockCount \ {bl};
        goto final;
    else
        bl:=bl+1;
    end if;
  end while;
final: return ;
end procedure;


procedure find_next_free_inode()
 begin 
 valueupdate:
 in := BGDT[0].bg_inode_bitmap;
 find_next__free_inode:
  while in < sb.inodes_per_group do
    if (inodeBitmap[in] = "FREE") then 
        BGDT[0].bg_inode_bitmap := in;
        change_inodetablevalue:
        BGDT[0].bg_inode_table := in;
        in := sb.inodes_per_group;
    else
        in:=in+1;
    end if;
  end while;
change_free_inode_count: 
BGDT[0].bg_free_inode_count :=BGDT[0].bg_free_inode_count - 1; 
rstval: in:=BGDT[0].bg_inode_bitmap;
final: 
return; 
end procedure;

procedure find_next_free_block()
begin 
blvalue: bl:= BGDT[0].bg_block_bitmap;
find_next__free_block:
  while bl < sb.blocks_per_group do
    if (blockBitmap[bl] = "FREE") then 
        BGDT[0].bg_block_bitmap := bl;
        bl := sb.blocks_per_group;
    else
        bl:=bl+1;
    end if;
  end while;
change_free_blockcount:
BGDT[0].bg_free_block_count := BGDT[0].bg_free_block_count - 1; 
blnewvalue: bl:= BGDT[0].bg_block_bitmap;
final: 
return;
end procedure;









procedure UpdateBGDT(command)
begin 
find_next_free_inode : call find_next_free_inode();
find_next_free_block : 
if command = "slink" then
          call find_next_free_block ()
   elsif command = "mkdir" then
          call find_next_free_block ()  
   end if;
final:
return;
end procedure;

procedure createDirEntry (name) begin 
create:
    de.inode := inode_num;
nanmelen:
    de.name_len := Len(name);
reclen:
    de.rec_len := ((8 + de.name_len + 3) * 4 )\div 4;
filename:
    de.filename := name;
back: 
return; 
end procedure;

procedure addDirEntry(name) 
begin 
create_dir_entry: 
call createDirEntry(name);
addDirEntry: 
dirlist := dirlist \o <<de>>; 
lenlist := lenlist +1; 
back:
return; 
end procedure;

procedure UpdateInode (command)
begin 
writeInode: 
    if InodeTable[inode_num].dtime = 0 then
      InodeTable[inode_num].dtime := -1;
      Inode_NUM: InodeTable[inode_num].iNum := inode_num;
      change_mode:
      if command = "slink" then
          InodeTable[inode_num].mode := "ext3_symlink";
      elsif command = "mkdir" then
          InodeTable[inode_num].mode := "ext2_dir";
      elsif command = "touch" then
          InodeTable[inode_num].mode := "ext2_reg";
       end if;
      init_block:
      if command = "slink" then
           InodeTable[inode_num].blocks := 1;
      elsif command = "mkdir" then
           InodeTable[inode_num].blocks := 1;
      elsif command = "touch" then
           InodeTable[inode_num].blocks := 0;
      end if;
      fstblock:
      if command = "slink" then
            InodeTable[inode_num].directAddr[0] := block_num;      
      elsif command = "mkdir" then
            InodeTable[inode_num].directAddr[0] := block_num;      
      end if;
      change_uid: InodeTable[inode_num].uid := 1000;
      change_gid: InodeTable[inode_num].gid := 1000;
      change_size: InodeTable[inode_num].size := InodeTable[inode_num].blocks*sb.log_block_size;
      change_access_time: InodeTable[inode_num].atime := 1;
      change_creation_time: InodeTable[inode_num].ctime := 1;
      change_modification_time: InodeTable[inode_num].mtime := 1;
      change_links_count: InodeTable[inode_num].links_count := 1;
      generation_type: InodeTable[inode_num].generation := 0;
      else
      print "Error: inode already in use";
    end if;    
goback: return;
    
end procedure;

procedure updateSuperblock(command)
begin 
updatefreeinode:
sbins.free_inodes_count := sbins.free_inodes_count -1;
updatefreeblocks:
if command = "slink" then
            sbins.free_blocks_count := sbins.free_blocks_count -1;   
      elsif command = "mkdir" then
            sbins.free_blocks_count := sbins.free_blocks_count -1;   
      end if;
goback:
return;
end procedure;

procedure CreateFile(command, name)
begin 
  FindInode: call FindFreeInode();
  FindBlock :
   if command = "slink" then
          call FindFreeBlock ()
   elsif command = "mkdir" then
          call FindFreeBlock ()  
   end if;
   writeinode: call UpdateInode(command);
   update_BGDT: call UpdateBGDT(command);
   createdirentry: call addDirEntry(name); 
   updatesuperblock : call updateSuperblock(command);
  goback: return;
end procedure;


process MAIN= "Main Process" begin 
symbolic_link:
call CreateFile("slink","symlink");
regularfile:
call CreateFile("touch","regfile");
directory:
call CreateFile("mkdir","directory1");

end
process;



end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "670c936e" /\ chksum(tla) = "44db6c1")
\* Label find of procedure FindFreeInode at line 42 col 3 changed to find_
\* Label final of procedure FindFreeInode at line 52 col 8 changed to final_
\* Label final of procedure FindFreeBlock at line 67 col 8 changed to final_F
\* Label final of procedure find_next_free_inode at line 90 col 1 changed to final_f
\* Label final of procedure find_next_free_block at line 109 col 1 changed to final_fi
\* Label find_next_free_inode of procedure UpdateBGDT at line 122 col 24 changed to find_next_free_inode_
\* Label find_next_free_block of procedure UpdateBGDT at line 124 col 1 changed to find_next_free_block_
\* Label back of procedure createDirEntry at line 143 col 1 changed to back_
\* Label addDirEntry of procedure addDirEntry at line 151 col 1 changed to addDirEntry_
\* Label goback of procedure UpdateInode at line 196 col 9 changed to goback_
\* Label goback of procedure updateSuperblock at line 211 col 1 changed to goback_u
\* Parameter command of procedure UpdateBGDT at line 120 col 22 changed to command_
\* Parameter name of procedure createDirEntry at line 133 col 27 changed to name_
\* Parameter name of procedure addDirEntry at line 146 col 23 changed to name_a
\* Parameter command of procedure UpdateInode at line 157 col 24 changed to command_U
\* Parameter command of procedure updateSuperblock at line 200 col 28 changed to command_u
CONSTANT defaultInitValue
VARIABLES inodeBitmap, blockBitmap, block_num, bl, in, FreeInodeCount, 
          FreeBlockCount, InodeTable, de, lenlist, dirlist, BGDT, sbins, 
          inode_num, pc, stack

(* define statement *)
FreeInodeExistsInvariant == \E i \in 0..sb.inodes_per_group-1 : inodeBitmap[i] = "FREE"
InodeInRange == de.inode \in 0..InodeCount-1
BlockNum == \E i \in 0..sb.inodes_per_group-1 : (InodeTable[i].blocks > 0 => \A j \in
0..InodeTable[i].blocks: InodeTable[i].directAddr[j] \in 0..sb.blocks_per_group-1)
FreeInodeCountProp == \A i \in FreeInodeCount: inodeBitmap[i] = "FREE"
FreeBlockCountProp == \A i \in FreeBlockCount: blockBitmap[i] = "FREE"
ValidRecLen == \A i \in 1..lenlist :dirlist[i].rec_len > 0
ValidNameLen == \A i \in 1..lenlist : dirlist[i].name_len >0
ValidFilename == \A i \in 1..lenlist : dirlist[i].filename # ""
max_file_size == \A i \in 0..sb.inodes_per_group-1 : InodeTable[i].size <= sb.blocks_per_group * sb.log_block_size
AllInodesCovered == [](\A i \in 0..sb.inodes_per_group-1 : inodeBitmap[i]\in {"FREE","ALLOCATED"})
AllblocksCovered == [](\A i \in 0..sb.blocks_per_group-1 : blockBitmap[i]\in {"FREE","ALLOCATED"})
ValidMode == [](\A i \in 0..sb.inodes_per_group-1 : InodeTable[i].mode \in {"ext2_reg", "ext2_dir", "ext2_symlink","none"})
InodeAllocation == [](\A i \in 0..sb.inodes_per_group-1 : InodeTable[i].dtime \in {0, -1})

VARIABLES command_, name_, name_a, command_U, command_u, command, name

vars == << inodeBitmap, blockBitmap, block_num, bl, in, FreeInodeCount, 
           FreeBlockCount, InodeTable, de, lenlist, dirlist, BGDT, sbins, 
           inode_num, pc, stack, command_, name_, name_a, command_U, 
           command_u, command, name >>

ProcSet == {"Main Process"}

Init == (* Global variables *)
        /\ inodeBitmap = [i \in 0..sb.inodes_per_group-1 |-> "FREE"]
        /\ blockBitmap = [i \in 0..sb.blocks_per_group-1 |-> "FREE"]
        /\ block_num = -1
        /\ bl = 0
        /\ in = 0
        /\ FreeInodeCount = {i \in 0..sb.inodes_per_group-1 : inodeBitmap[i] = "FREE"}
        /\ FreeBlockCount = {i \in 0..sb.blocks_per_group-1 : blockBitmap[i] = "FREE"}
        /\ InodeTable = [i \in 0..sb.inodes_per_group-1|->Inode]
        /\ de = dir_entry
        /\ lenlist = 0
        /\ dirlist = << >>
        /\ BGDT = BlockGroupDescriptorTable
        /\ sbins = sb
        /\ inode_num = -1
        (* Procedure UpdateBGDT *)
        /\ command_ = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure createDirEntry *)
        /\ name_ = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure addDirEntry *)
        /\ name_a = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure UpdateInode *)
        /\ command_U = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure updateSuperblock *)
        /\ command_u = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure CreateFile *)
        /\ command = [ self \in ProcSet |-> defaultInitValue]
        /\ name = [ self \in ProcSet |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "symbolic_link"]

find_(self) == /\ pc[self] = "find_"
               /\ IF in < sb.inodes_per_group
                     THEN /\ IF (inodeBitmap[in] = "FREE")
                                THEN /\ inodeBitmap' = [inodeBitmap EXCEPT ![in] = "ALLOCATED"]
                                     /\ inode_num' = in
                                     /\ FreeInodeCount' = FreeInodeCount \ {in}
                                     /\ pc' = [pc EXCEPT ![self] = "final_"]
                                     /\ in' = in
                                ELSE /\ in' = in+1
                                     /\ pc' = [pc EXCEPT ![self] = "find_"]
                                     /\ UNCHANGED << inodeBitmap, 
                                                     FreeInodeCount, inode_num >>
                     ELSE /\ pc' = [pc EXCEPT ![self] = "final_"]
                          /\ UNCHANGED << inodeBitmap, in, FreeInodeCount, 
                                          inode_num >>
               /\ UNCHANGED << blockBitmap, block_num, bl, FreeBlockCount, 
                               InodeTable, de, lenlist, dirlist, BGDT, sbins, 
                               stack, command_, name_, name_a, command_U, 
                               command_u, command, name >>

final_(self) == /\ pc[self] = "final_"
                /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                /\ UNCHANGED << inodeBitmap, blockBitmap, block_num, bl, in, 
                                FreeInodeCount, FreeBlockCount, InodeTable, de, 
                                lenlist, dirlist, BGDT, sbins, inode_num, 
                                command_, name_, name_a, command_U, command_u, 
                                command, name >>

FindFreeInode(self) == find_(self) \/ final_(self)

find(self) == /\ pc[self] = "find"
              /\ IF bl < sb.blocks_per_group
                    THEN /\ IF (blockBitmap[bl] = "FREE")
                               THEN /\ blockBitmap' = [blockBitmap EXCEPT ![bl] = "ALLOCATED"]
                                    /\ block_num' = bl
                                    /\ FreeBlockCount' = FreeBlockCount \ {bl}
                                    /\ pc' = [pc EXCEPT ![self] = "final_F"]
                                    /\ bl' = bl
                               ELSE /\ bl' = bl+1
                                    /\ pc' = [pc EXCEPT ![self] = "find"]
                                    /\ UNCHANGED << blockBitmap, block_num, 
                                                    FreeBlockCount >>
                    ELSE /\ pc' = [pc EXCEPT ![self] = "final_F"]
                         /\ UNCHANGED << blockBitmap, block_num, bl, 
                                         FreeBlockCount >>
              /\ UNCHANGED << inodeBitmap, in, FreeInodeCount, InodeTable, de, 
                              lenlist, dirlist, BGDT, sbins, inode_num, stack, 
                              command_, name_, name_a, command_U, command_u, 
                              command, name >>

final_F(self) == /\ pc[self] = "final_F"
                 /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                 /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                 /\ UNCHANGED << inodeBitmap, blockBitmap, block_num, bl, in, 
                                 FreeInodeCount, FreeBlockCount, InodeTable, 
                                 de, lenlist, dirlist, BGDT, sbins, inode_num, 
                                 command_, name_, name_a, command_U, command_u, 
                                 command, name >>

FindFreeBlock(self) == find(self) \/ final_F(self)

valueupdate(self) == /\ pc[self] = "valueupdate"
                     /\ in' = BGDT[0].bg_inode_bitmap
                     /\ pc' = [pc EXCEPT ![self] = "find_next__free_inode"]
                     /\ UNCHANGED << inodeBitmap, blockBitmap, block_num, bl, 
                                     FreeInodeCount, FreeBlockCount, 
                                     InodeTable, de, lenlist, dirlist, BGDT, 
                                     sbins, inode_num, stack, command_, name_, 
                                     name_a, command_U, command_u, command, 
                                     name >>

find_next__free_inode(self) == /\ pc[self] = "find_next__free_inode"
                               /\ IF in < sb.inodes_per_group
                                     THEN /\ IF (inodeBitmap[in] = "FREE")
                                                THEN /\ BGDT' = [BGDT EXCEPT ![0].bg_inode_bitmap = in]
                                                     /\ pc' = [pc EXCEPT ![self] = "change_inodetablevalue"]
                                                     /\ in' = in
                                                ELSE /\ in' = in+1
                                                     /\ pc' = [pc EXCEPT ![self] = "find_next__free_inode"]
                                                     /\ BGDT' = BGDT
                                     ELSE /\ pc' = [pc EXCEPT ![self] = "change_free_inode_count"]
                                          /\ UNCHANGED << in, BGDT >>
                               /\ UNCHANGED << inodeBitmap, blockBitmap, 
                                               block_num, bl, FreeInodeCount, 
                                               FreeBlockCount, InodeTable, de, 
                                               lenlist, dirlist, sbins, 
                                               inode_num, stack, command_, 
                                               name_, name_a, command_U, 
                                               command_u, command, name >>

change_inodetablevalue(self) == /\ pc[self] = "change_inodetablevalue"
                                /\ BGDT' = [BGDT EXCEPT ![0].bg_inode_table = in]
                                /\ in' = sb.inodes_per_group
                                /\ pc' = [pc EXCEPT ![self] = "find_next__free_inode"]
                                /\ UNCHANGED << inodeBitmap, blockBitmap, 
                                                block_num, bl, FreeInodeCount, 
                                                FreeBlockCount, InodeTable, de, 
                                                lenlist, dirlist, sbins, 
                                                inode_num, stack, command_, 
                                                name_, name_a, command_U, 
                                                command_u, command, name >>

change_free_inode_count(self) == /\ pc[self] = "change_free_inode_count"
                                 /\ BGDT' = [BGDT EXCEPT ![0].bg_free_inode_count = BGDT[0].bg_free_inode_count - 1]
                                 /\ pc' = [pc EXCEPT ![self] = "rstval"]
                                 /\ UNCHANGED << inodeBitmap, blockBitmap, 
                                                 block_num, bl, in, 
                                                 FreeInodeCount, 
                                                 FreeBlockCount, InodeTable, 
                                                 de, lenlist, dirlist, sbins, 
                                                 inode_num, stack, command_, 
                                                 name_, name_a, command_U, 
                                                 command_u, command, name >>

rstval(self) == /\ pc[self] = "rstval"
                /\ in' = BGDT[0].bg_inode_bitmap
                /\ pc' = [pc EXCEPT ![self] = "final_f"]
                /\ UNCHANGED << inodeBitmap, blockBitmap, block_num, bl, 
                                FreeInodeCount, FreeBlockCount, InodeTable, de, 
                                lenlist, dirlist, BGDT, sbins, inode_num, 
                                stack, command_, name_, name_a, command_U, 
                                command_u, command, name >>

final_f(self) == /\ pc[self] = "final_f"
                 /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                 /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                 /\ UNCHANGED << inodeBitmap, blockBitmap, block_num, bl, in, 
                                 FreeInodeCount, FreeBlockCount, InodeTable, 
                                 de, lenlist, dirlist, BGDT, sbins, inode_num, 
                                 command_, name_, name_a, command_U, command_u, 
                                 command, name >>

find_next_free_inode(self) == valueupdate(self)
                                 \/ find_next__free_inode(self)
                                 \/ change_inodetablevalue(self)
                                 \/ change_free_inode_count(self)
                                 \/ rstval(self) \/ final_f(self)

blvalue(self) == /\ pc[self] = "blvalue"
                 /\ bl' = BGDT[0].bg_block_bitmap
                 /\ pc' = [pc EXCEPT ![self] = "find_next__free_block"]
                 /\ UNCHANGED << inodeBitmap, blockBitmap, block_num, in, 
                                 FreeInodeCount, FreeBlockCount, InodeTable, 
                                 de, lenlist, dirlist, BGDT, sbins, inode_num, 
                                 stack, command_, name_, name_a, command_U, 
                                 command_u, command, name >>

find_next__free_block(self) == /\ pc[self] = "find_next__free_block"
                               /\ IF bl < sb.blocks_per_group
                                     THEN /\ IF (blockBitmap[bl] = "FREE")
                                                THEN /\ BGDT' = [BGDT EXCEPT ![0].bg_block_bitmap = bl]
                                                     /\ bl' = sb.blocks_per_group
                                                ELSE /\ bl' = bl+1
                                                     /\ BGDT' = BGDT
                                          /\ pc' = [pc EXCEPT ![self] = "find_next__free_block"]
                                     ELSE /\ pc' = [pc EXCEPT ![self] = "change_free_blockcount"]
                                          /\ UNCHANGED << bl, BGDT >>
                               /\ UNCHANGED << inodeBitmap, blockBitmap, 
                                               block_num, in, FreeInodeCount, 
                                               FreeBlockCount, InodeTable, de, 
                                               lenlist, dirlist, sbins, 
                                               inode_num, stack, command_, 
                                               name_, name_a, command_U, 
                                               command_u, command, name >>

change_free_blockcount(self) == /\ pc[self] = "change_free_blockcount"
                                /\ BGDT' = [BGDT EXCEPT ![0].bg_free_block_count = BGDT[0].bg_free_block_count - 1]
                                /\ pc' = [pc EXCEPT ![self] = "blnewvalue"]
                                /\ UNCHANGED << inodeBitmap, blockBitmap, 
                                                block_num, bl, in, 
                                                FreeInodeCount, FreeBlockCount, 
                                                InodeTable, de, lenlist, 
                                                dirlist, sbins, inode_num, 
                                                stack, command_, name_, name_a, 
                                                command_U, command_u, command, 
                                                name >>

blnewvalue(self) == /\ pc[self] = "blnewvalue"
                    /\ bl' = BGDT[0].bg_block_bitmap
                    /\ pc' = [pc EXCEPT ![self] = "final_fi"]
                    /\ UNCHANGED << inodeBitmap, blockBitmap, block_num, in, 
                                    FreeInodeCount, FreeBlockCount, InodeTable, 
                                    de, lenlist, dirlist, BGDT, sbins, 
                                    inode_num, stack, command_, name_, name_a, 
                                    command_U, command_u, command, name >>

final_fi(self) == /\ pc[self] = "final_fi"
                  /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                  /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                  /\ UNCHANGED << inodeBitmap, blockBitmap, block_num, bl, in, 
                                  FreeInodeCount, FreeBlockCount, InodeTable, 
                                  de, lenlist, dirlist, BGDT, sbins, inode_num, 
                                  command_, name_, name_a, command_U, 
                                  command_u, command, name >>

find_next_free_block(self) == blvalue(self) \/ find_next__free_block(self)
                                 \/ change_free_blockcount(self)
                                 \/ blnewvalue(self) \/ final_fi(self)

find_next_free_inode_(self) == /\ pc[self] = "find_next_free_inode_"
                               /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "find_next_free_inode",
                                                                        pc        |->  "find_next_free_block_" ] >>
                                                                    \o stack[self]]
                               /\ pc' = [pc EXCEPT ![self] = "valueupdate"]
                               /\ UNCHANGED << inodeBitmap, blockBitmap, 
                                               block_num, bl, in, 
                                               FreeInodeCount, FreeBlockCount, 
                                               InodeTable, de, lenlist, 
                                               dirlist, BGDT, sbins, inode_num, 
                                               command_, name_, name_a, 
                                               command_U, command_u, command, 
                                               name >>

find_next_free_block_(self) == /\ pc[self] = "find_next_free_block_"
                               /\ IF command_[self] = "slink"
                                     THEN /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "find_next_free_block",
                                                                                   pc        |->  "final" ] >>
                                                                               \o stack[self]]
                                          /\ pc' = [pc EXCEPT ![self] = "blvalue"]
                                     ELSE /\ IF command_[self] = "mkdir"
                                                THEN /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "find_next_free_block",
                                                                                              pc        |->  "final" ] >>
                                                                                          \o stack[self]]
                                                     /\ pc' = [pc EXCEPT ![self] = "blvalue"]
                                                ELSE /\ pc' = [pc EXCEPT ![self] = "final"]
                                                     /\ stack' = stack
                               /\ UNCHANGED << inodeBitmap, blockBitmap, 
                                               block_num, bl, in, 
                                               FreeInodeCount, FreeBlockCount, 
                                               InodeTable, de, lenlist, 
                                               dirlist, BGDT, sbins, inode_num, 
                                               command_, name_, name_a, 
                                               command_U, command_u, command, 
                                               name >>

final(self) == /\ pc[self] = "final"
               /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
               /\ command_' = [command_ EXCEPT ![self] = Head(stack[self]).command_]
               /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
               /\ UNCHANGED << inodeBitmap, blockBitmap, block_num, bl, in, 
                               FreeInodeCount, FreeBlockCount, InodeTable, de, 
                               lenlist, dirlist, BGDT, sbins, inode_num, name_, 
                               name_a, command_U, command_u, command, name >>

UpdateBGDT(self) == find_next_free_inode_(self)
                       \/ find_next_free_block_(self) \/ final(self)

create(self) == /\ pc[self] = "create"
                /\ de' = [de EXCEPT !.inode = inode_num]
                /\ pc' = [pc EXCEPT ![self] = "nanmelen"]
                /\ UNCHANGED << inodeBitmap, blockBitmap, block_num, bl, in, 
                                FreeInodeCount, FreeBlockCount, InodeTable, 
                                lenlist, dirlist, BGDT, sbins, inode_num, 
                                stack, command_, name_, name_a, command_U, 
                                command_u, command, name >>

nanmelen(self) == /\ pc[self] = "nanmelen"
                  /\ de' = [de EXCEPT !.name_len = Len(name_[self])]
                  /\ pc' = [pc EXCEPT ![self] = "reclen"]
                  /\ UNCHANGED << inodeBitmap, blockBitmap, block_num, bl, in, 
                                  FreeInodeCount, FreeBlockCount, InodeTable, 
                                  lenlist, dirlist, BGDT, sbins, inode_num, 
                                  stack, command_, name_, name_a, command_U, 
                                  command_u, command, name >>

reclen(self) == /\ pc[self] = "reclen"
                /\ de' = [de EXCEPT !.rec_len = ((8 + de.name_len + 3) * 4 )\div 4]
                /\ pc' = [pc EXCEPT ![self] = "filename"]
                /\ UNCHANGED << inodeBitmap, blockBitmap, block_num, bl, in, 
                                FreeInodeCount, FreeBlockCount, InodeTable, 
                                lenlist, dirlist, BGDT, sbins, inode_num, 
                                stack, command_, name_, name_a, command_U, 
                                command_u, command, name >>

filename(self) == /\ pc[self] = "filename"
                  /\ de' = [de EXCEPT !.filename = name_[self]]
                  /\ pc' = [pc EXCEPT ![self] = "back_"]
                  /\ UNCHANGED << inodeBitmap, blockBitmap, block_num, bl, in, 
                                  FreeInodeCount, FreeBlockCount, InodeTable, 
                                  lenlist, dirlist, BGDT, sbins, inode_num, 
                                  stack, command_, name_, name_a, command_U, 
                                  command_u, command, name >>

back_(self) == /\ pc[self] = "back_"
               /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
               /\ name_' = [name_ EXCEPT ![self] = Head(stack[self]).name_]
               /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
               /\ UNCHANGED << inodeBitmap, blockBitmap, block_num, bl, in, 
                               FreeInodeCount, FreeBlockCount, InodeTable, de, 
                               lenlist, dirlist, BGDT, sbins, inode_num, 
                               command_, name_a, command_U, command_u, command, 
                               name >>

createDirEntry(self) == create(self) \/ nanmelen(self) \/ reclen(self)
                           \/ filename(self) \/ back_(self)

create_dir_entry(self) == /\ pc[self] = "create_dir_entry"
                          /\ /\ name_' = [name_ EXCEPT ![self] = name_a[self]]
                             /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "createDirEntry",
                                                                      pc        |->  "addDirEntry_",
                                                                      name_     |->  name_[self] ] >>
                                                                  \o stack[self]]
                          /\ pc' = [pc EXCEPT ![self] = "create"]
                          /\ UNCHANGED << inodeBitmap, blockBitmap, block_num, 
                                          bl, in, FreeInodeCount, 
                                          FreeBlockCount, InodeTable, de, 
                                          lenlist, dirlist, BGDT, sbins, 
                                          inode_num, command_, name_a, 
                                          command_U, command_u, command, name >>

addDirEntry_(self) == /\ pc[self] = "addDirEntry_"
                      /\ dirlist' = dirlist \o <<de>>
                      /\ lenlist' = lenlist +1
                      /\ pc' = [pc EXCEPT ![self] = "back"]
                      /\ UNCHANGED << inodeBitmap, blockBitmap, block_num, bl, 
                                      in, FreeInodeCount, FreeBlockCount, 
                                      InodeTable, de, BGDT, sbins, inode_num, 
                                      stack, command_, name_, name_a, 
                                      command_U, command_u, command, name >>

back(self) == /\ pc[self] = "back"
              /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
              /\ name_a' = [name_a EXCEPT ![self] = Head(stack[self]).name_a]
              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
              /\ UNCHANGED << inodeBitmap, blockBitmap, block_num, bl, in, 
                              FreeInodeCount, FreeBlockCount, InodeTable, de, 
                              lenlist, dirlist, BGDT, sbins, inode_num, 
                              command_, name_, command_U, command_u, command, 
                              name >>

addDirEntry(self) == create_dir_entry(self) \/ addDirEntry_(self)
                        \/ back(self)

writeInode(self) == /\ pc[self] = "writeInode"
                    /\ IF InodeTable[inode_num].dtime = 0
                          THEN /\ InodeTable' = [InodeTable EXCEPT ![inode_num].dtime = -1]
                               /\ pc' = [pc EXCEPT ![self] = "Inode_NUM"]
                          ELSE /\ PrintT("Error: inode already in use")
                               /\ pc' = [pc EXCEPT ![self] = "goback_"]
                               /\ UNCHANGED InodeTable
                    /\ UNCHANGED << inodeBitmap, blockBitmap, block_num, bl, 
                                    in, FreeInodeCount, FreeBlockCount, de, 
                                    lenlist, dirlist, BGDT, sbins, inode_num, 
                                    stack, command_, name_, name_a, command_U, 
                                    command_u, command, name >>

Inode_NUM(self) == /\ pc[self] = "Inode_NUM"
                   /\ InodeTable' = [InodeTable EXCEPT ![inode_num].iNum = inode_num]
                   /\ pc' = [pc EXCEPT ![self] = "change_mode"]
                   /\ UNCHANGED << inodeBitmap, blockBitmap, block_num, bl, in, 
                                   FreeInodeCount, FreeBlockCount, de, lenlist, 
                                   dirlist, BGDT, sbins, inode_num, stack, 
                                   command_, name_, name_a, command_U, 
                                   command_u, command, name >>

change_mode(self) == /\ pc[self] = "change_mode"
                     /\ IF command_U[self] = "slink"
                           THEN /\ InodeTable' = [InodeTable EXCEPT ![inode_num].mode = "ext3_symlink"]
                           ELSE /\ IF command_U[self] = "mkdir"
                                      THEN /\ InodeTable' = [InodeTable EXCEPT ![inode_num].mode = "ext2_dir"]
                                      ELSE /\ IF command_U[self] = "touch"
                                                 THEN /\ InodeTable' = [InodeTable EXCEPT ![inode_num].mode = "ext2_reg"]
                                                 ELSE /\ TRUE
                                                      /\ UNCHANGED InodeTable
                     /\ pc' = [pc EXCEPT ![self] = "init_block"]
                     /\ UNCHANGED << inodeBitmap, blockBitmap, block_num, bl, 
                                     in, FreeInodeCount, FreeBlockCount, de, 
                                     lenlist, dirlist, BGDT, sbins, inode_num, 
                                     stack, command_, name_, name_a, command_U, 
                                     command_u, command, name >>

init_block(self) == /\ pc[self] = "init_block"
                    /\ IF command_U[self] = "slink"
                          THEN /\ InodeTable' = [InodeTable EXCEPT ![inode_num].blocks = 1]
                          ELSE /\ IF command_U[self] = "mkdir"
                                     THEN /\ InodeTable' = [InodeTable EXCEPT ![inode_num].blocks = 1]
                                     ELSE /\ IF command_U[self] = "touch"
                                                THEN /\ InodeTable' = [InodeTable EXCEPT ![inode_num].blocks = 0]
                                                ELSE /\ TRUE
                                                     /\ UNCHANGED InodeTable
                    /\ pc' = [pc EXCEPT ![self] = "fstblock"]
                    /\ UNCHANGED << inodeBitmap, blockBitmap, block_num, bl, 
                                    in, FreeInodeCount, FreeBlockCount, de, 
                                    lenlist, dirlist, BGDT, sbins, inode_num, 
                                    stack, command_, name_, name_a, command_U, 
                                    command_u, command, name >>

fstblock(self) == /\ pc[self] = "fstblock"
                  /\ IF command_U[self] = "slink"
                        THEN /\ InodeTable' = [InodeTable EXCEPT ![inode_num].directAddr[0] = block_num]
                        ELSE /\ IF command_U[self] = "mkdir"
                                   THEN /\ InodeTable' = [InodeTable EXCEPT ![inode_num].directAddr[0] = block_num]
                                   ELSE /\ TRUE
                                        /\ UNCHANGED InodeTable
                  /\ pc' = [pc EXCEPT ![self] = "change_uid"]
                  /\ UNCHANGED << inodeBitmap, blockBitmap, block_num, bl, in, 
                                  FreeInodeCount, FreeBlockCount, de, lenlist, 
                                  dirlist, BGDT, sbins, inode_num, stack, 
                                  command_, name_, name_a, command_U, 
                                  command_u, command, name >>

change_uid(self) == /\ pc[self] = "change_uid"
                    /\ InodeTable' = [InodeTable EXCEPT ![inode_num].uid = 1000]
                    /\ pc' = [pc EXCEPT ![self] = "change_gid"]
                    /\ UNCHANGED << inodeBitmap, blockBitmap, block_num, bl, 
                                    in, FreeInodeCount, FreeBlockCount, de, 
                                    lenlist, dirlist, BGDT, sbins, inode_num, 
                                    stack, command_, name_, name_a, command_U, 
                                    command_u, command, name >>

change_gid(self) == /\ pc[self] = "change_gid"
                    /\ InodeTable' = [InodeTable EXCEPT ![inode_num].gid = 1000]
                    /\ pc' = [pc EXCEPT ![self] = "change_size"]
                    /\ UNCHANGED << inodeBitmap, blockBitmap, block_num, bl, 
                                    in, FreeInodeCount, FreeBlockCount, de, 
                                    lenlist, dirlist, BGDT, sbins, inode_num, 
                                    stack, command_, name_, name_a, command_U, 
                                    command_u, command, name >>

change_size(self) == /\ pc[self] = "change_size"
                     /\ InodeTable' = [InodeTable EXCEPT ![inode_num].size = InodeTable[inode_num].blocks*sb.log_block_size]
                     /\ pc' = [pc EXCEPT ![self] = "change_access_time"]
                     /\ UNCHANGED << inodeBitmap, blockBitmap, block_num, bl, 
                                     in, FreeInodeCount, FreeBlockCount, de, 
                                     lenlist, dirlist, BGDT, sbins, inode_num, 
                                     stack, command_, name_, name_a, command_U, 
                                     command_u, command, name >>

change_access_time(self) == /\ pc[self] = "change_access_time"
                            /\ InodeTable' = [InodeTable EXCEPT ![inode_num].atime = 1]
                            /\ pc' = [pc EXCEPT ![self] = "change_creation_time"]
                            /\ UNCHANGED << inodeBitmap, blockBitmap, 
                                            block_num, bl, in, FreeInodeCount, 
                                            FreeBlockCount, de, lenlist, 
                                            dirlist, BGDT, sbins, inode_num, 
                                            stack, command_, name_, name_a, 
                                            command_U, command_u, command, 
                                            name >>

change_creation_time(self) == /\ pc[self] = "change_creation_time"
                              /\ InodeTable' = [InodeTable EXCEPT ![inode_num].ctime = 1]
                              /\ pc' = [pc EXCEPT ![self] = "change_modification_time"]
                              /\ UNCHANGED << inodeBitmap, blockBitmap, 
                                              block_num, bl, in, 
                                              FreeInodeCount, FreeBlockCount, 
                                              de, lenlist, dirlist, BGDT, 
                                              sbins, inode_num, stack, 
                                              command_, name_, name_a, 
                                              command_U, command_u, command, 
                                              name >>

change_modification_time(self) == /\ pc[self] = "change_modification_time"
                                  /\ InodeTable' = [InodeTable EXCEPT ![inode_num].mtime = 1]
                                  /\ pc' = [pc EXCEPT ![self] = "change_links_count"]
                                  /\ UNCHANGED << inodeBitmap, blockBitmap, 
                                                  block_num, bl, in, 
                                                  FreeInodeCount, 
                                                  FreeBlockCount, de, lenlist, 
                                                  dirlist, BGDT, sbins, 
                                                  inode_num, stack, command_, 
                                                  name_, name_a, command_U, 
                                                  command_u, command, name >>

change_links_count(self) == /\ pc[self] = "change_links_count"
                            /\ InodeTable' = [InodeTable EXCEPT ![inode_num].links_count = 1]
                            /\ pc' = [pc EXCEPT ![self] = "generation_type"]
                            /\ UNCHANGED << inodeBitmap, blockBitmap, 
                                            block_num, bl, in, FreeInodeCount, 
                                            FreeBlockCount, de, lenlist, 
                                            dirlist, BGDT, sbins, inode_num, 
                                            stack, command_, name_, name_a, 
                                            command_U, command_u, command, 
                                            name >>

generation_type(self) == /\ pc[self] = "generation_type"
                         /\ InodeTable' = [InodeTable EXCEPT ![inode_num].generation = 0]
                         /\ pc' = [pc EXCEPT ![self] = "goback_"]
                         /\ UNCHANGED << inodeBitmap, blockBitmap, block_num, 
                                         bl, in, FreeInodeCount, 
                                         FreeBlockCount, de, lenlist, dirlist, 
                                         BGDT, sbins, inode_num, stack, 
                                         command_, name_, name_a, command_U, 
                                         command_u, command, name >>

goback_(self) == /\ pc[self] = "goback_"
                 /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                 /\ command_U' = [command_U EXCEPT ![self] = Head(stack[self]).command_U]
                 /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                 /\ UNCHANGED << inodeBitmap, blockBitmap, block_num, bl, in, 
                                 FreeInodeCount, FreeBlockCount, InodeTable, 
                                 de, lenlist, dirlist, BGDT, sbins, inode_num, 
                                 command_, name_, name_a, command_u, command, 
                                 name >>

UpdateInode(self) == writeInode(self) \/ Inode_NUM(self)
                        \/ change_mode(self) \/ init_block(self)
                        \/ fstblock(self) \/ change_uid(self)
                        \/ change_gid(self) \/ change_size(self)
                        \/ change_access_time(self)
                        \/ change_creation_time(self)
                        \/ change_modification_time(self)
                        \/ change_links_count(self)
                        \/ generation_type(self) \/ goback_(self)

updatefreeinode(self) == /\ pc[self] = "updatefreeinode"
                         /\ sbins' = [sbins EXCEPT !.free_inodes_count = sbins.free_inodes_count -1]
                         /\ pc' = [pc EXCEPT ![self] = "updatefreeblocks"]
                         /\ UNCHANGED << inodeBitmap, blockBitmap, block_num, 
                                         bl, in, FreeInodeCount, 
                                         FreeBlockCount, InodeTable, de, 
                                         lenlist, dirlist, BGDT, inode_num, 
                                         stack, command_, name_, name_a, 
                                         command_U, command_u, command, name >>

updatefreeblocks(self) == /\ pc[self] = "updatefreeblocks"
                          /\ IF command_u[self] = "slink"
                                THEN /\ sbins' = [sbins EXCEPT !.free_blocks_count = sbins.free_blocks_count -1]
                                ELSE /\ IF command_u[self] = "mkdir"
                                           THEN /\ sbins' = [sbins EXCEPT !.free_blocks_count = sbins.free_blocks_count -1]
                                           ELSE /\ TRUE
                                                /\ sbins' = sbins
                          /\ pc' = [pc EXCEPT ![self] = "goback_u"]
                          /\ UNCHANGED << inodeBitmap, blockBitmap, block_num, 
                                          bl, in, FreeInodeCount, 
                                          FreeBlockCount, InodeTable, de, 
                                          lenlist, dirlist, BGDT, inode_num, 
                                          stack, command_, name_, name_a, 
                                          command_U, command_u, command, name >>

goback_u(self) == /\ pc[self] = "goback_u"
                  /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                  /\ command_u' = [command_u EXCEPT ![self] = Head(stack[self]).command_u]
                  /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                  /\ UNCHANGED << inodeBitmap, blockBitmap, block_num, bl, in, 
                                  FreeInodeCount, FreeBlockCount, InodeTable, 
                                  de, lenlist, dirlist, BGDT, sbins, inode_num, 
                                  command_, name_, name_a, command_U, command, 
                                  name >>

updateSuperblock(self) == updatefreeinode(self) \/ updatefreeblocks(self)
                             \/ goback_u(self)

FindInode(self) == /\ pc[self] = "FindInode"
                   /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "FindFreeInode",
                                                            pc        |->  "FindBlock" ] >>
                                                        \o stack[self]]
                   /\ pc' = [pc EXCEPT ![self] = "find_"]
                   /\ UNCHANGED << inodeBitmap, blockBitmap, block_num, bl, in, 
                                   FreeInodeCount, FreeBlockCount, InodeTable, 
                                   de, lenlist, dirlist, BGDT, sbins, 
                                   inode_num, command_, name_, name_a, 
                                   command_U, command_u, command, name >>

FindBlock(self) == /\ pc[self] = "FindBlock"
                   /\ IF command[self] = "slink"
                         THEN /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "FindFreeBlock",
                                                                       pc        |->  "writeinode" ] >>
                                                                   \o stack[self]]
                              /\ pc' = [pc EXCEPT ![self] = "find"]
                         ELSE /\ IF command[self] = "mkdir"
                                    THEN /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "FindFreeBlock",
                                                                                  pc        |->  "writeinode" ] >>
                                                                              \o stack[self]]
                                         /\ pc' = [pc EXCEPT ![self] = "find"]
                                    ELSE /\ pc' = [pc EXCEPT ![self] = "writeinode"]
                                         /\ stack' = stack
                   /\ UNCHANGED << inodeBitmap, blockBitmap, block_num, bl, in, 
                                   FreeInodeCount, FreeBlockCount, InodeTable, 
                                   de, lenlist, dirlist, BGDT, sbins, 
                                   inode_num, command_, name_, name_a, 
                                   command_U, command_u, command, name >>

writeinode(self) == /\ pc[self] = "writeinode"
                    /\ /\ command_U' = [command_U EXCEPT ![self] = command[self]]
                       /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "UpdateInode",
                                                                pc        |->  "update_BGDT",
                                                                command_U |->  command_U[self] ] >>
                                                            \o stack[self]]
                    /\ pc' = [pc EXCEPT ![self] = "writeInode"]
                    /\ UNCHANGED << inodeBitmap, blockBitmap, block_num, bl, 
                                    in, FreeInodeCount, FreeBlockCount, 
                                    InodeTable, de, lenlist, dirlist, BGDT, 
                                    sbins, inode_num, command_, name_, name_a, 
                                    command_u, command, name >>

update_BGDT(self) == /\ pc[self] = "update_BGDT"
                     /\ /\ command_' = [command_ EXCEPT ![self] = command[self]]
                        /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "UpdateBGDT",
                                                                 pc        |->  "createdirentry",
                                                                 command_  |->  command_[self] ] >>
                                                             \o stack[self]]
                     /\ pc' = [pc EXCEPT ![self] = "find_next_free_inode_"]
                     /\ UNCHANGED << inodeBitmap, blockBitmap, block_num, bl, 
                                     in, FreeInodeCount, FreeBlockCount, 
                                     InodeTable, de, lenlist, dirlist, BGDT, 
                                     sbins, inode_num, name_, name_a, 
                                     command_U, command_u, command, name >>

createdirentry(self) == /\ pc[self] = "createdirentry"
                        /\ /\ name_a' = [name_a EXCEPT ![self] = name[self]]
                           /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "addDirEntry",
                                                                    pc        |->  "updatesuperblock",
                                                                    name_a    |->  name_a[self] ] >>
                                                                \o stack[self]]
                        /\ pc' = [pc EXCEPT ![self] = "create_dir_entry"]
                        /\ UNCHANGED << inodeBitmap, blockBitmap, block_num, 
                                        bl, in, FreeInodeCount, FreeBlockCount, 
                                        InodeTable, de, lenlist, dirlist, BGDT, 
                                        sbins, inode_num, command_, name_, 
                                        command_U, command_u, command, name >>

updatesuperblock(self) == /\ pc[self] = "updatesuperblock"
                          /\ /\ command_u' = [command_u EXCEPT ![self] = command[self]]
                             /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "updateSuperblock",
                                                                      pc        |->  "goback",
                                                                      command_u |->  command_u[self] ] >>
                                                                  \o stack[self]]
                          /\ pc' = [pc EXCEPT ![self] = "updatefreeinode"]
                          /\ UNCHANGED << inodeBitmap, blockBitmap, block_num, 
                                          bl, in, FreeInodeCount, 
                                          FreeBlockCount, InodeTable, de, 
                                          lenlist, dirlist, BGDT, sbins, 
                                          inode_num, command_, name_, name_a, 
                                          command_U, command, name >>

goback(self) == /\ pc[self] = "goback"
                /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                /\ command' = [command EXCEPT ![self] = Head(stack[self]).command]
                /\ name' = [name EXCEPT ![self] = Head(stack[self]).name]
                /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                /\ UNCHANGED << inodeBitmap, blockBitmap, block_num, bl, in, 
                                FreeInodeCount, FreeBlockCount, InodeTable, de, 
                                lenlist, dirlist, BGDT, sbins, inode_num, 
                                command_, name_, name_a, command_U, command_u >>

CreateFile(self) == FindInode(self) \/ FindBlock(self) \/ writeinode(self)
                       \/ update_BGDT(self) \/ createdirentry(self)
                       \/ updatesuperblock(self) \/ goback(self)

symbolic_link == /\ pc["Main Process"] = "symbolic_link"
                 /\ /\ command' = [command EXCEPT !["Main Process"] = "slink"]
                    /\ name' = [name EXCEPT !["Main Process"] = "symlink"]
                    /\ stack' = [stack EXCEPT !["Main Process"] = << [ procedure |->  "CreateFile",
                                                                       pc        |->  "regularfile",
                                                                       command   |->  command["Main Process"],
                                                                       name      |->  name["Main Process"] ] >>
                                                                   \o stack["Main Process"]]
                 /\ pc' = [pc EXCEPT !["Main Process"] = "FindInode"]
                 /\ UNCHANGED << inodeBitmap, blockBitmap, block_num, bl, in, 
                                 FreeInodeCount, FreeBlockCount, InodeTable, 
                                 de, lenlist, dirlist, BGDT, sbins, inode_num, 
                                 command_, name_, name_a, command_U, command_u >>

regularfile == /\ pc["Main Process"] = "regularfile"
               /\ /\ command' = [command EXCEPT !["Main Process"] = "touch"]
                  /\ name' = [name EXCEPT !["Main Process"] = "regfile"]
                  /\ stack' = [stack EXCEPT !["Main Process"] = << [ procedure |->  "CreateFile",
                                                                     pc        |->  "directory",
                                                                     command   |->  command["Main Process"],
                                                                     name      |->  name["Main Process"] ] >>
                                                                 \o stack["Main Process"]]
               /\ pc' = [pc EXCEPT !["Main Process"] = "FindInode"]
               /\ UNCHANGED << inodeBitmap, blockBitmap, block_num, bl, in, 
                               FreeInodeCount, FreeBlockCount, InodeTable, de, 
                               lenlist, dirlist, BGDT, sbins, inode_num, 
                               command_, name_, name_a, command_U, command_u >>

directory == /\ pc["Main Process"] = "directory"
             /\ /\ command' = [command EXCEPT !["Main Process"] = "mkdir"]
                /\ name' = [name EXCEPT !["Main Process"] = "directory1"]
                /\ stack' = [stack EXCEPT !["Main Process"] = << [ procedure |->  "CreateFile",
                                                                   pc        |->  "Done",
                                                                   command   |->  command["Main Process"],
                                                                   name      |->  name["Main Process"] ] >>
                                                               \o stack["Main Process"]]
             /\ pc' = [pc EXCEPT !["Main Process"] = "FindInode"]
             /\ UNCHANGED << inodeBitmap, blockBitmap, block_num, bl, in, 
                             FreeInodeCount, FreeBlockCount, InodeTable, de, 
                             lenlist, dirlist, BGDT, sbins, inode_num, 
                             command_, name_, name_a, command_U, command_u >>

MAIN == symbolic_link \/ regularfile \/ directory

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == MAIN
           \/ (\E self \in ProcSet:  \/ FindFreeInode(self) \/ FindFreeBlock(self)
                                     \/ find_next_free_inode(self)
                                     \/ find_next_free_block(self)
                                     \/ UpdateBGDT(self) \/ createDirEntry(self)
                                     \/ addDirEntry(self) \/ UpdateInode(self)
                                     \/ updateSuperblock(self) \/ CreateFile(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Tue Jul 18 16:44:44 EEST 2023 by mateo
\* Created Sun Mar 05 20:47:12 EET 2023 by mateo
