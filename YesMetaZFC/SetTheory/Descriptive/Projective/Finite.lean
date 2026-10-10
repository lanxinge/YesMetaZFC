import YesMetaZFC.SetTheory.Descriptive.Projective.ProjectionClosure

/-! # ZF 中各层的二元布尔码运算

二元指标上的见证选择由两次存在消去直接构造；不调用 AC_ω(B)。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem fcc_empty_l {B H : M.Domain} (hh : ∀ x, ¬ M.mem x H) : Fcc_d I B H := by
  intro D hd R _
  have he i : ¬ M.mem i D := fun hi => ((hd i).mp hi).elim fun _ hp => hp.elim fun p hp => hh p hp.2
  exact ⟨D, ds_empty_fun_l I he, fun i x h => (he i ((ds_empty_fun_l I (X := B) he).input_mem_of_pairMember h)).elim⟩

theorem two_family_l (hKP : M.Models KP) {z o : M.Domain} (hzo : z ≠ o) (p q : M.Domain) :
    ∃ H, M.IsSetFunction I H ∧ ∀ i r, M.PairMember I i r H ↔ (i = z ∧ r = p) ∨ (i = o ∧ r = q) := by
  obtain ⟨a, ha⟩ := I.total z p
  obtain ⟨b, hb⟩ := I.total o q
  obtain ⟨H, hh⟩ := KP.exists_pair hKP a b
  have pair i r : M.PairMember I i r H ↔ (i = z ∧ r = p) ∨ (i = o ∧ r = q) :=
    ⟨fun ⟨c, hc, hcH⟩ => ((hh c).mp hcH).elim (fun e => Or.inl (I.injective (e ▸ hc) ha))
      (fun e => Or.inr (I.injective (e ▸ hc) hb)), fun h => h.elim
      (fun ⟨rfl, rfl⟩ => ⟨a, ha, (hh a).mpr (Or.inl rfl)⟩) (fun ⟨rfl, rfl⟩ => ⟨b, hb, (hh b).mpr (Or.inr rfl)⟩)⟩
  refine ⟨H, ⟨fun c hc => ((hh c).mp hc).elim (fun e => ⟨z, p, e.symm ▸ ha⟩) (fun e => ⟨o, q, e.symm ▸ hb⟩), ?_⟩, pair⟩
  intro i r s hr hs
  rcases (pair i r).mp hr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases (pair _ s).mp hs with ⟨hi, rfl⟩ | ⟨hi, rfl⟩
  · rfl
  · exact (hzo hi).elim
  · exact (hzo hi.symm).elim
  · rfl

theorem fcc_two_l (hKP : M.Models KP) {B H z o p q} (hzo : z ≠ o)
    (hh : ∀ i r, M.PairMember I i r H ↔ (i = z ∧ r = p) ∨ (i = o ∧ r = q)) : Fcc_d I B H := by
  intro D hd R total
  have hz := (hd z).mpr ⟨p, (hh z p).mpr (Or.inl ⟨rfl, rfl⟩)⟩
  have ho := (hd o).mpr ⟨q, (hh o q).mpr (Or.inr ⟨rfl, rfl⟩)⟩
  obtain ⟨a, ha, hza⟩ := total z hz
  obtain ⟨b, hb, hob⟩ := total o ho
  obtain ⟨F, hf, ef⟩ := two_family_l I hKP hzo a b
  have dom : M.IsDomainOf I D F := fun i => (hd i).trans
    ⟨fun ⟨r, hr⟩ => ((hh i r).mp hr).elim (fun h => ⟨a, (ef i a).mpr (Or.inl ⟨h.1, rfl⟩)⟩)
      (fun h => ⟨b, (ef i b).mpr (Or.inr ⟨h.1, rfl⟩)⟩),
      fun ⟨r, hr⟩ => ((ef i r).mp hr).elim (fun h => ⟨p, (hh i p).mpr (Or.inl ⟨h.1, rfl⟩)⟩)
        (fun h => ⟨q, (hh i q).mpr (Or.inr ⟨h.1, rfl⟩)⟩)⟩
  refine ⟨F, ⟨hf, dom, fun i hi => ?_⟩, fun i r hr => ?_⟩
  · obtain ⟨r, hr⟩ := (dom i).mp hi
    exact ⟨r, ((ef i r).mp hr).elim (fun h => h.2.symm ▸ ha) (fun h => h.2.symm ▸ hb), hr⟩
  · exact ((ef i r).mp hr).elim (fun ⟨e, h⟩ => e.symm ▸ h.symm ▸ hza) (fun ⟨e, h⟩ => e.symm ▸ h.symm ▸ hob)

theorem pc_binary_l (hZF : M.Models ZF) {ω A B J n t p q} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (ha : M.CardinalLessOrEqual I A ω) (hJ : Npair_d I ω J)
    (hp : Pc_d I ω A n t p) (hq : Pc_d I ω A n t q) (b : Bool) :
    ∃ r K, Pc_d I ω A n t r ∧ Pden_d I ω A B J r K ∧ ∀ x, M.mem x K ↔ M.mem x B ∧
      (if b then Pev_d I ω A B J p x ∨ Pev_d I ω A B J q x else Pev_d I ω A B J p x ∧ Pev_d I ω A B J q x) := by
  obtain ⟨z, hz, hzω⟩ := hB.1.1.1
  obtain ⟨o, ho, hoω⟩ := hB.1.1.2 z hzω
  have hzo : z ≠ o := fun e => hz z (e.symm ▸ ho.predecessor_mem)
  obtain ⟨H, hh, eh⟩ := two_family_l I (ZF.modelsKP hZF) hzo p q
  have fam : Pf_d I ω A n t H := ⟨hp.1, hp.2.1, hh, fun i r hr => ((eh i r).mp hr).elim
    (fun ⟨e, h⟩ => ⟨e.symm ▸ hzω, h.symm ▸ hp.2.2⟩) (fun ⟨e, h⟩ => ⟨e.symm ▸ hoω, h.symm ▸ hq.2.2⟩)⟩
  obtain ⟨r, K, hr, hk, val⟩ := pf_countable_with_l I hZF hB hA ha hJ (fcc_two_l I (ZF.modelsKP hZF) hzo eh) fam b
  refine ⟨r, K, hr, hk, fun x => (val x).trans (and_congr_right fun _ => ?_)⟩
  cases b
  · exact ⟨fun h => ⟨h z p ((eh z p).mpr (Or.inl ⟨rfl, rfl⟩)), h o q ((eh o q).mpr (Or.inr ⟨rfl, rfl⟩))⟩,
      fun h i s hs => ((eh i s).mp hs).elim (fun e => e.2.symm ▸ h.1) (fun e => e.2.symm ▸ h.2)⟩
  · exact ⟨fun ⟨i, s, hs, hx⟩ => ((eh i s).mp hs).elim (fun e => Or.inl (e.2 ▸ hx)) (fun e => Or.inr (e.2 ▸ hx)),
      fun h => h.elim (fun h => ⟨z, p, (eh z p).mpr (Or.inl ⟨rfl, rfl⟩), h⟩)
        (fun h => ⟨o, q, (eh o q).mpr (Or.inr ⟨rfl, rfl⟩), h⟩)⟩

/-- 空并为空，空交为全空间；任意内部层号都不需要选择公理。 -/
theorem pc_empty_family_l (hZF : M.Models ZF) {ω A B J n t H} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (ha : M.CardinalLessOrEqual I A ω) (hJ : Npair_d I ω J)
    (hn : M.mem n ω) (ht : (∀ x, ¬ M.mem x t) ∨ M.IsOrdinalOne t)
    (hh : ∀ x, ¬ M.mem x H) (b : Bool) : ∃ q K, Pc_d I ω A n t q ∧ Pden_d I ω A B J q K ∧
      ∀ x, M.mem x K ↔ b = false ∧ M.mem x B := by
  have no_pair i p : ¬ M.PairMember I i p H := fun ⟨r, _, hr⟩ => hh r hr
  have fam : Pf_d I ω A n t H := ⟨hn, ht, (ds_empty_fun_l I (X := ω) hh).1,
    fun i p hp => (no_pair i p hp).elim⟩
  obtain ⟨q, K, hq, hk, val⟩ := pf_countable_with_l I hZF hB hA ha hJ (fcc_empty_l I hh) fam b
  refine ⟨q, K, hq, hk, fun x => ?_⟩
  cases b <;> simpa [no_pair] using val x

theorem pd_binary_l (hZF : M.Models ZF) {ω A B J n K L} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (ha : M.CardinalLessOrEqual I A ω) (hJ : Npair_d I ω J)
    (hn : M.mem n ω) (hk : Pd_d I ω A B J n K) (hl : Pd_d I ω A B J n L) (b : Bool) :
    ∃ V, Pd_d I ω A B J n V ∧ ∀ x, M.mem x V ↔
      (if b then M.mem x K ∨ M.mem x L else M.mem x K ∧ M.mem x L) := by
  obtain ⟨z, hz, _⟩ := hB.1.1.1
  obtain ⟨o, ho, _⟩ := hB.1.exists_ordinalOne_mem
  obtain ⟨p, hp, hpk⟩ := (pc_sigma_l I hn hz).mp hk.1
  obtain ⟨q, hq, hql⟩ := (pc_sigma_l I hn hz).mp hl.1
  obtain ⟨r, hr, hrk⟩ := (pc_pi_l I hn ho).mp hk.2
  obtain ⟨s, hs, hsl⟩ := (pc_pi_l I hn ho).mp hl.2
  obtain ⟨a, U, hau, hu, eu⟩ := pc_binary_l I hZF hB hA ha hJ hp hq b
  obtain ⟨c, V, hcv, hv, ev⟩ := pc_binary_l I hZF hB hA ha hJ hr hs b
  have uv x : M.mem x U ↔ M.mem x V := by
    rw [eu x, ev x, ← pev_mem_l I hZF hB.1 hpk, ← pev_mem_l I hZF hB.1 hql,
      ← pev_mem_l I hZF hB.1 hrk, ← pev_mem_l I hZF hB.1 hsl]
  have e := hZF.1.eq_of_same_members V U (fun x => (uv x).symm)
  subst V
  refine ⟨U, ⟨(pc_sigma_l I hn hz).mpr ⟨a, hau, hu⟩, (pc_pi_l I hn ho).mpr ⟨c, hcv, hv⟩⟩, fun x => ?_⟩
  rw [eu x, ← pev_mem_l I hZF hB.1 hpk, ← pev_mem_l I hZF hB.1 hql]
  refine ⟨And.right, fun h => ⟨?_, h⟩⟩
  cases b
  · exact ps_subset_l I hk.1 x h.1
  · exact h.elim (ps_subset_l I hk.1 x) (ps_subset_l I hl.1 x)

end YesMetaZFC.SetTheory.Descriptive
