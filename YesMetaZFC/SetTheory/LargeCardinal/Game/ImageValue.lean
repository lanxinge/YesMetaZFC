import YesMetaZFC.Model.SetTheory.Relations.CollectCode

/-! # 实际初等图中的目标函数值回拉

目标取值先见证原生存在公式。初等性给出源中的实际求值，图的全定义性再给出其像，
目标函数单值性将这个像识别为原目标值；源仅需外延性，无需额外集合论模型假设。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Smap_d.value_preimage_l {ω c X R d N W j a b s t y : M.Domain}
    (hw : M.IsOmega ω) (source : Smdl_d I c X R) (target : Smem_d I d N W)
    (nt : M.TransitiveSet N) (map : Smap_d I ω c d X N j) (ext : Rf_ext_d I X R)
    (ia : Rd_entry_d a b j) (is : Rd_entry_d s t j) (fn : M.IsSetFunction I t)
    (value : Rd_entry_d b y t) : ∃ x, Rf_val_d I X R a x s ∧ Rd_entry_d x y j := by
  let A := smdl_structure_l I (R := R) source.2.1
  let B := smdl_structure_l I (R := W) target.1.2.1
  have ea := ext.native_l I source.2.1
  have eb := (rf_ext_mem_l I hZF.1 nt target).native_l I target.1.2.1
  let an : A.Domain := ⟨a,map.1.1.input_mem_of_pairMember ia⟩
  let sn : A.Domain := ⟨s,map.1.1.input_mem_of_pairMember is⟩
  let bn : B.Domain := ⟨b,map.1.1.output_mem_of_pairMember ia⟩
  let tn : B.Domain := ⟨t,map.1.1.output_mem_of_pairMember is⟩
  have val := (rf_val_mem_l I hZF.1 nt target tn.property).mpr value
  let yn : B.Domain := ⟨y,(val.bounds_l I).2.1⟩
  let ρ : Env A 2 := ⟨Fin.cases an (fun _ => sn),fun _ => sn⟩
  let η : Env B 2 := ⟨Fin.cases bn (fun _ => tn),fun _ => tn⟩
  let φ : Formula 1 2 := .existsE (rd_entry0_m (.bound 1) .newest (.bound 2))
  have transfer := smap_source_l I hZF hw source target.1 map φ
    (by simp -implicitDefEqProofs [φ,Definitional.Formula.FreeClosed]) ρ η (Fin.cases ia (fun _ => is))
  have exists_value : Formula.satisfies η φ := ⟨yn,
    (rd_entry0_sat_l eb (η.push yn) (.bound 1) .newest (.bound 2)).mpr
      ((rf_val_native_l I target.1.2.1 eb bn yn tn).mp val)⟩
  obtain ⟨x,hx⟩ := transfer.mpr exists_value
  have read : Rf_val_d I X R a x.val s := (rf_val_native_l I source.2.1 ea an x sn).mpr
    ((rd_entry0_sat_l ea (ρ.push x) (.bound 1) .newest (.bound 2)).mp hx)
  obtain ⟨y',_,image⟩ := map.1.1.2.2 x.val x.property
  have moved := read.map_l I hZF hw source target.1 map ia image is
  have entry := (rf_val_mem_l I hZF.1 nt target tn.property).mp moved
  exact ⟨x.val,read,fn.2 b y' y entry value ▸ image⟩

end YesMetaZFC.SetTheory.LargeCardinal
