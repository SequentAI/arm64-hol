/* Flat identity memory for the A64 user-space (EL0) model.

   Replaces stage 1 and stage 2 address translation with the identity map,
   as armv8.6-asl-snapshot commit 7b8e94ba did for the Armv8.6-A model.
   Memory accesses use the full 64-bit virtual address (see the accompanying
   patch to interface.sail and mem.sail), mapped as Normal write-back
   memory with no fault. */

function AArch64_TranslateAddress (va, accdesc, aligned, size) = {
    wb : MemAttrHints = undefined;
    wb.attrs = MemAttr_WB;
    wb.hints = MemHint_RWA;
    wb.transient = false;
    memattrs : MemoryAttributes = undefined;
    memattrs.memtype = MemType_Normal;
    memattrs.inner = wb;
    memattrs.outer = wb;
    memattrs.shareability = Shareability_ISH;
    memattrs.tags = MemTag_Untagged;
    memattrs.notagaccess = false;
    memattrs.xs = 0b0;
    let pa : FullAddress = struct { paspace = PAS_NonSecure, address = va[55 .. 0] };
    return(CreateAddressDescriptor(va, pa, memattrs))
}
