with Ada.Containers.Functional_Vectors;

with TLSF.Block.Types; use TLSF.Block.Types;
with TLSF.Config; use TLSF.Config;

package TLSF.Block.Proof with  SPARK_Mode, Ghost is
   
   pragma Unevaluated_Use_Of_Old (Allow);

   package Formal_Model with SPARK_Mode, Ghost is
      use Ada.Containers;
      subtype Positive_Count_Type is Count_Type range 1 .. Count_Type'Last;
           
      -- each block is unique charecterized by its address
      
      package Va is new Ada.Containers.Functional_Vectors
        (Element_Type => Address,
         Index_Type   => Positive_Count_Type);
      
       function "="
        (Left  : Va.Sequence;
         Right : Va.Sequence) return Boolean renames Va."=";

      function "<"
        (Left  : Va.Sequence;
         Right : Va.Sequence) return Boolean renames Va."<";

      function "<="
        (Left  : Va.Sequence;
         Right : Va.Sequence) return Boolean renames Va."<=";
      
      function Find_Address (V : Va.Sequence; Addr : Address) return Count_Type
      --  Search for Address
      with
        Global => null,
        Post =>
            (if Find_Address'Result > 0 then
               Find_Address'Result <= Va.Length (V)
             and Addr = Va.Get (V, Find_Address'Result));

      function Address_Present(V : Va.Sequence; Addr : Address) return Boolean
      is (Find_Address(V, Addr) > 0);
      
      
   end Formal_Model;
   
   
   function Hash (Addr : Address) return Ada.Containers.Hash_Type is
     (Ada.Containers.Hash_Type(Addr));
   
   package Block_Map is new Ada.Containers.Formal_Hashed_Maps
     (Key_Type        => Address,
      Element_Type    => Block_Header,
      Hash            => Hash);

   package Free_Blocks_Set is new Ada.Containers.Formal_Hashed_Sets
     (Element_Type        => Address,
      Hash                => Hash);

   use type Ada.Containers.Count_Type;
   
   use type Free_Blocks_Set.Set;

   subtype Map is Block_Map.Map(Capacity => 1024, Modulus => 0);
   subtype Set is Free_Blocks_Set.Set(Capacity => 1024, Modulus => 0);
   
   Empty_Set : Set renames Free_Blocks_Set.Empty_Set;
   
   type Free_Lists_Type
   is array (First_Level_Index, Second_Level_Index) of Set;
      
   type Proof_State_Type is record
      Blocks       : Map;
      Free_Lists   : Free_Lists_Type;
   end record;

   Proof_State : Proof_State_Type;
   
   function Block_Present_At_Address(Addr : Valid_Address)
                                     return Boolean
     with Global => Proof_State,
     Contract_Cases => 
       ( (Block_Map.Contains(Proof_State.Blocks, Addr)) =>
           Block_Present_At_Address'Result = True,
         others                                         => 
           Block_Present_At_Address'Result = False);

   function Block_At_Address (Addr : Valid_Address) return Block_Header
     with Global => Proof_State, 
     Pre => Block_Present_At_Address(Addr),
     Post => Block_At_Address'Result = 
       Block_Map.Element(Proof_State.Blocks, Addr);

   function Specific_Block_Present_At_Address(Addr  : Valid_Address;
                                              Block : Block_Header)
                                              return Boolean
     with Global => Proof_State,
     Contract_Cases => 
       ( Block_Present_At_Address(Addr) and then 
               Block_At_Address(Addr) = Block => 
               Specific_Block_Present_At_Address'Result = True,
         others                         => 
           Specific_Block_Present_At_Address'Result = False);
      
   procedure Put_Block_At_Address (Addr : Valid_Address; Block : Block_Header)
     with Global => (In_Out => Proof_State),
     Pre => not Block_Present_At_Address(Addr) and then
     Block_Map.Length(Proof_State.Blocks) < Proof_State.Blocks.Capacity,
     Post => (Block_Present_At_Address(Addr) and then
                  Block_At_Address(Addr) = Block);
   
   procedure Remove_Block_At_Address(Addr : Valid_Address)
     with Pre => Block_Present_At_Address(Addr),
     Post => not Block_Present_At_Address(Addr);

   -- working with free lists
                 
   function Get_Free_List (FL_Idx : First_Level_Index;
                           SL_Idx : Second_Level_Index)
                           return Set
   is (Proof_State.Free_Lists (FL_Idx, SL_Idx));

   function Get_Free_List (Index : Level_Index) return Set
   is (Get_Free_List(Index.First_Level, Index.Second_Level));
   
   function Get_Free_List (Sz : Size) return Set
   is (Get_Free_List(Calculate_Levels_Indices(Size_Bits(Sz))))
     with Pre => Sz >= Small_Block_Size;
   
   function Is_Block_Present_In_Free_Lists
     (Addr : Valid_Address)
      return Boolean
     with 
       Global => Proof_State,
       Contract_Cases =>
         ( not (for all FL_Idx in First_Level_Index'Range => (
                        for all SL_Idx in Second_Level_Index'Range =>
                  (if Free_Blocks_Set.Contains(Get_Free_List(FL_Idx, SL_Idx), Addr)
                       then False))) => Is_Block_Present_In_Free_Lists'Result = True,
           others           =>
             Is_Block_Present_In_Free_Lists'Result = False);
   
   function Is_Block_In_Free_List_For_Size
     (Sz   : Size;
      Addr : Valid_Address)
      return Boolean
     with 
       Global => (Input => Proof_State),
     Pre => Sz >= Small_Block_Size,
     Contract_Cases => 
       ( Free_Blocks_Set.Contains(Get_Free_List(Sz), Addr) =>
           Is_Block_In_Free_List_For_Size'Result = True,
         others                                            =>
           Is_Block_In_Free_List_For_Size'Result = False);

   function Is_Block_Present_In_Exactly_One_Free_List_For_Size
     (Sz   : Size;
      Addr : Valid_Address)
      return Boolean
     with 
       Global => (Input => Proof_State),
     Pre => Sz >= Small_Block_Size;
   -- TODO: Add quantified postcondition

   procedure Remove_Block_From_Free_List_For_Size
     (Sz   : Size;
      Addr : Valid_Address)
     with 
       Global => (In_Out => Proof_State),
     Pre => Sz >= Small_Block_Size and then
     Is_Block_In_Free_List_For_Size(Sz, Addr),
     Post => not Is_Block_In_Free_List_For_Size(Sz, Addr);
   
   procedure Put_Block_In_Free_List_For_Size
     (Sz   : Size;
      Addr : Valid_Address)
     with
       Global => (In_Out => Proof_State),
     Pre => Sz >= Small_Block_Size and then
     not Is_Block_In_Free_List_For_Size(Sz, Addr),
     Post => Is_Block_In_Free_List_For_Size(Sz, Addr);

end TLSF.Block.Proof;
