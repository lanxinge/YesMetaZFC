import YesMetaZFC.Model.SetTheory.Internal.OrdinalFoldSource
import YesMetaZFC.Model.SetTheory.Internal.SyntaxSource
import YesMetaZFC.Model.SetTheory.Internal.CanonicalRows

/-! # 合法程序的逐行自然数编码在极限秩层中绝对 -/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

theorem sc_node_natural_l {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)
    (hZF : M.Models ZF) {ω r c z} (hω : M.IsOmega ω) (hr : M.mem r ω)
    (hc : Sfm_node_d I ω r c) (hz : Sc_node_d I c z) : M.mem z ω := by
  obtain ⟨k, p, i, j, t, code, args, ht, hz⟩ := hz
  have nk := sfm_node_components_l I hZF hω hr hc code args
  exact oc_pair_natural_l I hZF hω nk.1 (oc_pair_natural_l I hZF hω nk.2.1 nk.2.2 ht) hz

variable (hZF : M.Models ZF) {δ Z : M.Domain} (hδ : M.IsLimitOrdinal δ)
  (hV : V_d (kp_pair_l (ZF.modelsKP hZF)) δ Z) (nz : Nonempty {x // M.mem x Z})
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
local notation "T" => ZF.v_transitive_l I hZF hV
local notation "P" => sc_v_pair_l hZF hδ hV
local notation "N" => rt_model_l Z nz
local notation "J" => rt_pair_l T nz (And.left hZF) P

theorem rt_sc_node_up_l (c z : (N).Domain) (h : Sc_node_d J c z) : Sc_node_d I c.val z.val := by
  obtain ⟨k, p, i, j, t, hc, hp, ht, hz⟩ := h
  have code := rt_kpair_l hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) T nz P
  exact ⟨k.val, p.val, i.val, j.val, t.val, (code ..).mp hc, (code ..).mp hp,
    (rt_oc_pair_l hZF hδ hV nz ..).mp ht, (rt_oc_pair_l hZF hδ hV nz ..).mp hz⟩

theorem rt_sc_node_l (ω r c z : (N).Domain) (hω : M.IsOmega ω.val) (hr : M.mem r.val ω.val)
    (h : Sfm_node_d I ω.val r.val c.val) : Sc_node_d J c z ↔ Sc_node_d I c.val z.val := by
  refine ⟨rt_sc_node_up_l hZF hδ hV nz c z, ?_⟩
  rintro ⟨k, p, i, j, t, hc, hp, ht, hz⟩
  have nk := sfm_node_components_l I hZF hω hr h hc hp
  have nt := oc_pair_natural_l I hZF hω nk.2.1 nk.2.2 ht
  have kp := hc.mem_l M T c.property
  have ij := hp.mem_l M T kp.2
  have code := rt_kpair_l hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) T nz P
  exact ⟨⟨k, kp.1⟩, ⟨p, kp.2⟩, ⟨i, ij.1⟩, ⟨j, ij.2⟩, ⟨t, T ω.val ω.property t nt⟩,
    (code ..).mpr hc, (code ..).mpr hp, (rt_oc_pair_l hZF hδ hV nz ..).mpr ht,
    (rt_oc_pair_l hZF hδ hV nz ..).mpr hz⟩

theorem rt_sc_rows_l (ω n F G : (N).Domain) (hω : M.IsOmega ω.val)
    (hf : Sfm_d I ω.val n.val F.val) :
    Sc_rows_d J ω n F G ↔ Sc_rows_d I ω.val n.val F.val G.val := by
  have ent := rt_entry_l T nz hZF.1
  refine and_congr (rt_function_from_l T nz hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) P G n ω) ?_
  constructor
  · intro h r z
    constructor
    · intro hrz
      have rz := rd_entry_transitive_l T G.property hrz
      obtain ⟨hr, c, hrc, hc⟩ := (h ⟨r, rz.1⟩ ⟨z, rz.2⟩).mp ((ent ..).mpr hrz)
      exact ⟨hr, c.val, (ent ..).mp hrc, rt_sc_node_up_l hZF hδ hV nz c _ hc⟩
    · rintro ⟨hr, c, hrc, hc⟩
      have rc := rd_entry_transitive_l T F.property hrc
      have nr := hω.transitive hZF n.val hf.1 r hr
      have node := hf.2.2 r c hrc
      let r' : (N).Domain := ⟨r, rc.1⟩
      let c' : (N).Domain := ⟨c, rc.2⟩
      let z' : (N).Domain := ⟨z, T ω.val ω.property z (sc_node_natural_l I hZF hω nr node hc)⟩
      exact (ent ..).mp ((h r' z').mpr
        ⟨hr, c', (ent ..).mpr hrc, (rt_sc_node_l hZF hδ hV nz ω r' c' z' hω nr node).mpr hc⟩)
  · intro h r z
    refine (ent r z G).trans ((h r.val z.val).trans (and_congr_right fun hr => ?_))
    constructor
    · rintro ⟨c, hrc, hc⟩
      let c' : (N).Domain := ⟨c, (rd_entry_transitive_l T F.property hrc).2⟩
      exact ⟨c', (ent ..).mpr hrc, (rt_sc_node_l hZF hδ hV nz ω r c' z hω
        (hω.transitive hZF n.val hf.1 r.val hr) (hf.2.2 r.val c hrc)).mpr hc⟩
    · rintro ⟨c, hrc, hc⟩
      exact ⟨c.val, (ent ..).mp hrc, rt_sc_node_up_l hZF hδ hV nz c z hc⟩

end YesMetaZFC.SetTheory.Internal
