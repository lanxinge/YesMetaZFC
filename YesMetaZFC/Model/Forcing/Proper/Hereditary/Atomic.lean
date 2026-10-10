import YesMetaZFC.Model.Forcing.Proper.Hereditary.AtomicWitness
import YesMetaZFC.Model.Forcing.Internal.Reflection.Transitive
import YesMetaZFC.Model.Forcing.Internal.Atomic.Witness

/-! # H(χ) 中名称与原子力迫的绝对性

反向解释的存在见证由遗传小支撑与双模拟定理实际给出；其余量词由传递性覆盖。
因此内部初等性可直接消费原子的力迫公式，不必假设 H(χ) 满足幂集公理。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.Internal
universe u
variable {M : SetTheory.Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kpair_interpretation_l M (And.left hZFC) (KP.exists_pair (ZF.modelsKP hZF))
variable {ω χ H c T : M.Domain} (hω : M.IsOmega ω)
  (hχ : M.IsRegularCardinal (kpair_interpretation_l M hZFC.1
    (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) χ) (hωχ : M.mem ω χ)
  (hH : H_d (kpair_interpretation_l M hZFC.1 (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) χ H)
  (hM : Smdl_d (kpair_interpretation_l M hZFC.1 (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) c H T)
  (hT : ∀ x y, M.PairMember (kpair_interpretation_l M hZFC.1
    (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) x y T ↔ M.mem x H ∧ M.mem y H ∧ M.mem x y)
local notation "L" => smdl_structure_l I (R := T) (And.left (And.right hM))
local notation "htr" => ZF.h_transitive_l I hZF hH
include hω hχ hωχ hH hT

theorem smem_name_l (B t : (L).Domain) : Name_d L B t ↔ Name_d M B.val t.val := by
  constructor
  · rintro ⟨S, ht, hS⟩
    exact ⟨S.val, (smem_member_l I hM hT t S).mp ht, (smem_supp_l I hM hT htr B S).mp hS⟩
  · intro ht
    obtain ⟨S, htS, _, hS, hSH⟩ := h_support_l hZFC hω hχ hωχ hH ht ht t.property t.property
    let S' : (L).Domain := ⟨S, hSH⟩
    exact ⟨S', (smem_member_l I hM hT t S').mpr htS, (smem_supp_l I hM hT htr B S').mpr hS⟩

theorem smem_eq_force_l (B R z p s t : (L).Domain) (hs : Name_d M B.val s.val) (ht : Name_d M B.val t.val) :
    Eq_force_d L B R z p s t ↔ Eq_force_d M B.val R.val z.val p.val s.val t.val := by
  constructor
  · rintro ⟨hp, F, hF, hst⟩
    exact ⟨(smem_member_l I hM hT p B).mp hp, F.val, (smem_bisim_l I hM hT htr B R z F).mp hF,
      (smem_rel_l I hM hT htr F p s t).mp hst⟩
  · intro h
    obtain ⟨F, hFH, hF, hst⟩ := h_eq_witness_l hZFC hω hχ hωχ hH B.property hs ht s.property t.property h
    let F' : (L).Domain := ⟨F, hFH⟩
    exact ⟨(smem_member_l I hM hT p B).mpr h.1, F', (smem_bisim_l I hM hT htr B R z F').mpr hF,
      (smem_rel_l I hM hT htr F' p s t).mpr hst⟩

theorem smem_mem_force_l (B R z p s t : (L).Domain) (hs : Name_d M B.val s.val) (ht : Name_d M B.val t.val) :
    Mem_force_d L B R z p s t ↔ Mem_force_d M B.val R.val z.val p.val s.val t.val := by
  constructor
  · rintro ⟨hp, h⟩
    refine ⟨(smem_member_l I hM hT p B).mp hp, fun q hq => ?_⟩
    let q' : (L).Domain := ⟨q, htr B.val B.property q hq.1⟩
    obtain ⟨r, a, b, hr, hab, hrb, he⟩ := h q' ((smem_below_l I hM hT htr B R z q' p).mpr hq)
    have hab' := (smem_entry_l I hM hT htr a b t).mp hab
    exact ⟨r.val, a.val, b.val, (smem_below_l I hM hT htr B R z r q').mp hr, hab',
      (smem_entry_l I hM hT htr r b R).mp hrb,
      (smem_eq_force_l hZFC hω hχ hωχ hH hM hT B R z r s a hs (name_entry_l M ht hab').1).mp he⟩
  · rintro ⟨hp, h⟩
    refine ⟨(smem_member_l I hM hT p B).mpr hp, fun q hq => ?_⟩
    obtain ⟨r, a, b, hr, hab, hrb, he⟩ := h q.val ((smem_below_l I hM hT htr B R z q p).mp hq)
    let r' : (L).Domain := ⟨r, htr B.val B.property r hr.1⟩
    let a' : (L).Domain := ⟨a, (trans_entry_l htr t.property hab).1⟩
    let b' : (L).Domain := ⟨b, (trans_entry_l htr t.property hab).2⟩
    exact ⟨r', a', b', (smem_below_l I hM hT htr B R z r' q).mpr hr,
      (smem_entry_l I hM hT htr a' b' t).mpr hab, (smem_entry_l I hM hT htr r' b' R).mpr hrb,
      (smem_eq_force_l hZFC hω hχ hωχ hH hM hT B R z r' s a' hs (name_entry_l M ht hab).1).mpr he⟩

theorem smem_wit_l (B R z p s t : (L).Domain) (hs : Name_d M B.val s.val) (ht : Name_d M B.val t.val) :
    Wit_d L false B R z p s t ↔ Wit_d M false B.val R.val z.val p.val s.val t.val := by
  constructor
  · rintro ⟨a, b, hab, hpb, he⟩
    have hab' := (smem_entry_l I hM hT htr a b t).mp hab
    exact ⟨a.val, b.val, hab', (smem_entry_l I hM hT htr p b R).mp hpb,
      (smem_eq_force_l hZFC hω hχ hωχ hH hM hT B R z p s a hs (name_entry_l M ht hab').1).mp he⟩
  · rintro ⟨a, b, hab, hpb, he⟩
    let a' : (L).Domain := ⟨a, (trans_entry_l htr t.property hab).1⟩
    let b' : (L).Domain := ⟨b, (trans_entry_l htr t.property hab).2⟩
    exact ⟨a', b', (smem_entry_l I hM hT htr a' b' t).mpr hab, (smem_entry_l I hM hT htr p b' R).mpr hpb,
      (smem_eq_force_l hZFC hω hχ hωχ hH hM hT B R z p s a' hs (name_entry_l M ht hab).1).mpr he⟩

end YesMetaZFC.Model.Forcing.Internal
