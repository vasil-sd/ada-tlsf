with System;
with TLSF.Block.Types;

package TLSF.Context with SPARK_Mode, Pure, Preelaborate is

   package BT renames TLSF.Block.Types;
   
   type Memory_Context is
      record
         Base        : System.Address;
         Region      : BT.Address_Space;
      end record;

   type Context is
      record
         Memory : Memory_Context;
      end record;
   
end TLSF.Context;
