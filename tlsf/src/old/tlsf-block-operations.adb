with System.Storage_Elements;

package body TLSF.Block.Operations with SPARK_Mode is
                 
   package SSE renames System.Storage_Elements;

   function Get_System_Address(Base : System.Address;
                               Addr : Address)
                               return System.Address 
     with SPARK_Mode => Off
   is
      use type SSE.Integer_Address;
      
      Base_Int   : constant SSE.Integer_Address := SSE.To_Integer(Base);
      Addr_Int   : constant SSE.Integer_Address :=
                   Base_Int + SSE.Integer_Address(Addr);
      Final_Addr : constant System.Address := SSE.To_Address(Addr_Int);
   begin
      return Final_Addr;
   end Get_System_Address;

   ---------------------------------
   -- Physical presence of blocks --
   ---------------------------------
   
   function Get_Block_At_Address(Base : System.Address;
                                 Addr : Aligned_Address)
                                 return Block_Header
     with SPARK_Mode => Off
   is      
      Block      : Block_Header 
        with Import, Address => Get_System_Address(Base, Addr);
   begin
      return Block;
   end Get_Block_At_Address;

   procedure Real_Set_Block_At_Address(Base   : System.Address;
                                       Addr   : Aligned_Address;
                                       Header : Block_Header)
     with Pre => Addr /= Address_Null;
   
   
   procedure Real_Set_Block_At_Address(Base   : System.Address;
                                       Addr   : Aligned_Address;
                                       Header : Block_Header)
     with SPARK_Mode => Off
   is
      Block      : Block_Header 
        with Import, Address => Get_System_Address(Base, Addr);
   begin
      Block := Header;
   end Real_Set_Block_At_Address;
   
   procedure Set_Block_At_Address(Base   : System.Address;
                                  Addr   : Aligned_Address;
                                  Header : Block_Header)
   is
   begin
      Real_Set_Block_At_Address(Base, Addr, Header);
      Proof.Put_Block_At_Address(Addr, Header);
   end Set_Block_At_Address;
   
   procedure Remove_Block_At_Address(Base : System.Address;
                                     Addr : Aligned_Address)
   is
      pragma Unreferenced(Base);
   begin
      Proof.Remove_Block_At_Address(Addr);
      -- read deletion is not performed - it is useless, may be only for security
      -- reasons
   end Remove_Block_At_Address;

   procedure Test is
      B : Block_Header;
      C : Block_Header := Block_Header'(Status             => Occupied,
                                        Prev_Block_Address => Address_Null,
                                        Prev_Block_Status  => Absent,
                                        Next_Block_Status  => Free,
                                        Size               => 1);
      A : System.Address := SSE.To_Address(0);
   begin
      Set_Block_At_Address(A, 0, C);
      pragma Assert(Proof.Block_Present_At_Address(0));
      pragma Assert(Proof.Block_At_Address(0) = C);
   end Test;

   
   ---------------------------
   -- Work with Free Blocks --
   ---------------------------
   
   procedure Unlink_From_Free_List (Base      : System.Address;
                                    Address   : Aligned_Address;
                                    Block     : in out Block_Header;
                                    Free_List : in out Free_Blocks_List)
   is
      Prev_Address : constant Aligned_Address := Block.Free_List.Prev_Address;
      Next_Address : constant Aligned_Address := Block.Free_List.Next_Address;
   begin
      pragma Assert(Proof.Block_Present_At_Address(Address));
      Remove_Block_At_Address(Base, Address);
      Proof.Remove_Block_From_Free_List_For_Size(Block.Size, Address);
      if Is_Block_Last_In_Free_List(Block) then
         Block.Free_List := Empty_Free_List;
         Free_List := Empty_Free_List;
      else
         declare
            Prev_Block : Block_Header := Get_Block_At_Address(Base, Prev_Address);
            Next_Block : Block_Header := Get_Block_At_Address(Base, Next_Address);
         begin
            Remove_Block_At_Address(Base, Prev_Address);
            Remove_Block_At_Address(Base, Next_Address);
            
            Prev_Block.Free_List.Next_Address := Next_Address;
            Next_Block.Free_List.Prev_Address := Prev_Address;
            
            Set_Block_At_Address(Base, Prev_Address, Prev_Block);
            Set_Block_At_Address(Base, Next_Address, Next_Block);
         end;
      end if;
      Set_Block_At_Address(Base, Address, Block);
   end Unlink_From_Free_List;

end TLSF.Block.Operations;
