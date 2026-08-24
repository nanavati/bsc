
`ifdef BSV_NO_Z
  `define BSV_GENC True
`else
  `define BSV_GENC genC
`endif

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

package ZBusUtil;

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

export ZBit;
export mkZBit;
export zBitGetWord;
export bitToZBit;
export zBitToBit;
export ConvertToZ(..);
export mkConvertToZ;
export ConvertFromZ(..);
export mkConvertFromZ;
export ResolveZ(..);
export mkResolveZ;
export ZDrive(..);
export ZResolve(..);
export mkZResolve;

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

typedef struct {
		t word;
		} ZBit #(type t) deriving (Eq, Bits);

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

function ZBit#(t) mkZBit(t w);
   return ((ZBit { word : w}));
endfunction

function t zBitGetWord(ZBit#(t) wz);
   return (wz.word);
endfunction

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

interface ConvertToZ #(type i);
   method ZBit#(i) convert(i x1, Bool x2);
endinterface

import "BVI" ConvertToZ = module vMkConvertToZ (ConvertToZ#(i))
			  provisos (Bits#(i,si));
                             default_clock clk();
			     parameter width = valueOf(si);
			     no_reset;
			     method OUT convert(IN, CTL);
                                schedule convert CF convert ;
			  endmodule

module mkConvertToZ(ConvertToZ#(i))
   provisos (Eq#(i), Bits#(i, si));
   ConvertToZ#(i) ifc;
   if (`BSV_GENC)
      ifc = interface ConvertToZ
	       method convert(word, enable) ;
		  return (bitToZBit(word, enable));
	       endmethod
	    endinterface;
   else begin
      ConvertToZ#(i) _a();
      vMkConvertToZ inst__a(_a);
      ifc = _a;
   end
   return (ifc);
endmodule

function ZBit#(i) bitToZBit(i word, Bool enable)
   provisos (Eq#(i), Bits#(i, si));
   return ((enable ? mkZBit(word) : mkZBit(unpack(0))));
endfunction

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

interface ConvertFromZ #(type i);
   method i convert(ZBit#(i) x1);
endinterface

import "BVI" ConvertFromZ = module vMkConvertFromZ (ConvertFromZ#(i))
			    provisos (Bits#(i,si));
                               default_clock clk();
			       parameter width = valueOf(si);
			       no_reset;
			       method OUT convert(IN);
			       schedule convert CF convert;
			    endmodule

module mkConvertFromZ(ConvertFromZ#(i))
   provisos (Eq#(i), Bits#(i, si1));
   ConvertFromZ#(i) ifc;
   if (`BSV_GENC)
      ifc = interface ConvertFromZ
	       method convert(k) ;
		  return (zBitToBit(k));
	       endmethod
	    endinterface;
   else begin
      ConvertFromZ#(i) _a();
      vMkConvertFromZ inst__a(_a);
      ifc = _a;
   end
   return (ifc);
endmodule

function i zBitToBit(ZBit#(i) wz)
   provisos (Eq#(i));
   return (zBitGetWord(wz));
endfunction

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

interface ResolveZ #(type i);
   method ZBit#(i) resolve(ZBit#(i) x1, ZBit#(i) x2);
endinterface: ResolveZ

import "BVI" ResolveZ = module vMkResolveZ  (ResolveZ#(i))
			provisos (Bits#(i,si));
                           default_clock clk();
			   parameter width = valueOf(si);
			   no_reset;
			   method OUT resolve(IN_0, IN_1);
                              schedule resolve CF resolve;
			endmodule

module mkResolveZ(ResolveZ#(i))
   provisos (Eq#(i), Bits#(i, si));
   ResolveZ#(i) ifc;
   if (`BSV_GENC)
      ifc = interface ResolveZ
	       method resolve(in_0, in_1) ;
		  return (resolveZ(in_0, in_1));
	       endmethod
	    endinterface;
   else begin
      ResolveZ#(i) _a();
      vMkResolveZ inst__a(_a);
      ifc = _a;
   end
   return (ifc);
endmodule

function ZBit#(i) resolveZ(ZBit#(i) wz_0, ZBit#(i) wz_1)
  provisos (Eq#(i), Bits#(i, si));
  return (mkZBit(unpack(pack(zBitGetWord(wz_0)) | pack(zBitGetWord(wz_1)))));
endfunction

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

// A resolution node taking (value, enable) PAIRS, so the generated
// Verilog keeps every Z inside the primitive (ZResolveNode.v): a
// structural two-state simulator only analyzes tri-state where the 'bz
// literals and the resolved net share a module, so a Z VALUE carried
// through ordinary ports degrades resolution into a dropped driver.
// The result pairs the resolved (enable-masked) value with the
// combined driven-ness.

typedef struct {
		Bool ctl;
		ZBit#(t) value;
		} ZDrive #(type t) deriving (Eq, Bits);

interface ZResolve #(type i);
   method ZDrive#(i) resolve(ZBit#(i) x1, Bool c1, ZBit#(i) x2, Bool c2);
endinterface: ZResolve

import "BVI" ZResolveNode = module vMkZResolve (ZResolve#(i))
			    provisos (Bits#(i,si));
                               default_clock clk();
			       parameter width = valueOf(si);
			       no_reset;
			       method OUT resolve(IN_0, CTL_0, IN_1, CTL_1);
                                  schedule resolve CF resolve;
			    endmodule

module mkZResolve(ZResolve#(i))
   provisos (Eq#(i), Bits#(i, si));
   ZResolve#(i) ifc;
   if (`BSV_GENC)
      ifc = interface ZResolve
	       method resolve(in_0, c_0, in_1, c_1) ;
		  return (ZDrive { ctl : (c_0 || c_1), value : resolveZ(in_0, in_1) });
	       endmethod
	    endinterface;
   else begin
      ZResolve#(i) _a();
      vMkZResolve inst__a(_a);
      ifc = _a;
   end
   return (ifc);
endmodule

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

endpackage

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////
