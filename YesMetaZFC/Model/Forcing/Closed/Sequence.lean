import YesMetaZFC.Model.Forcing.Closed.Syntax
import YesMetaZFC.Model.Forcing.Internal.Names.SequenceForcing
import YesMetaZFC.Model.Forcing.Internal.Reflection.Criterion
import YesMetaZFC.Model.Forcing.Internal.Ground.Transfer

/-! # 固定条件下名称下降链的逐项装配

同一条件已经迫使所有坐标属于后继偏序，并迫使较晚坐标低于较早坐标。
实际名称序列装配将这些证书合成扩张中的完整内部 ω 下降链。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}}

def Nchain_d (I : kpair_convention_l.Interpretation M) (B R z p ω A T f : M.Domain) : Prop :=
  M.IsSetFunction I f ∧ M.IsDomainOf I ω f ∧
    (∀ i s, Entry_d M i s f → Name_d M B s ∧ Mem_force_d M B R z p s A) ∧
    ∀ i j s t, M.mem i j → Entry_d M i s f → Entry_d M j t f → Rel_force_d M B R z T p t s

def nchain_m {n} (B R z p ω A T f : Term n) : Formula 1 n :=
  .conj (Formula.isFunction kpair_convention_l f) (.conj (Formula.isDomain kpair_convention_l ω f)
    (.conj (.forallE (.forallE (.imp (entry_m (.bound 1) .newest f.weaken.weaken)
      (.conj (name_m B.weaken.weaken .newest)
        (mem_force_m B.weaken.weaken R.weaken.weaken z.weaken.weaken p.weaken.weaken .newest A.weaken.weaken)))))
      (.forallE (.forallE (.forallE (.forallE (.imp (.mem (.bound 3) (.bound 2))
        (.imp (entry_m (.bound 3) (.bound 1) f.weaken.weaken.weaken.weaken)
          (.imp (entry_m (.bound 2) .newest f.weaken.weaken.weaken.weaken)
            (rel_force_m B.weaken.weaken.weaken.weaken R.weaken.weaken.weaken.weaken z.weaken.weaken.weaken.weaken
              T.weaken.weaken.weaken.weaken p.weaken.weaken.weaken.weaken .newest (.bound 1)))))))))))
derive_free_closed nchain_m

theorem nchain_sat_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M) {n}
    (ρ : Env M n) (B R z p ω A T f : Term n) : Formula.satisfies ρ (nchain_m B R z p ω A T f) ↔
      Nchain_d I (B.eval ρ) (R.eval ρ) (z.eval ρ) (p.eval ρ) (ω.eval ρ) (A.eval ρ) (T.eval ρ) (f.eval ρ) := by
  simp only [nchain_m, Nchain_d, Formula.satisfies_conj_iff, Formula.satisfies_isFunction_iff I hE,
    Formula.satisfies_isDomain_iff I, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    entry_sat_l M hE, name_sat_l M hE, mem_force_sat_l M hE, Formula.satisfies_mem_iff,
    rel_force_sat_l M hE, Definitional.Term.eval_weaken]
  rfl

variable {B R z : M.Domain} {U : M.Domain → Prop}
variable (O : Cond_order_d M B R z) (hZF : M.Models ZF) (hU : Generic_d M B R z U)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))
local notation "E" => extension_l M hZF B R z U
local notation "J" => kpair_interpretation_l E (extension_ext_l O hZF hU) (internal_pair_l O hZF hU)

theorem nchain_value_l {b p ω A T f t w} (hb : U b) (hp : U p)
    (hf : Nchain_d I B R z p ω A T f) (ht : Nseq_d M B b f t) (hw : Check_d M b ω w)
    {W Q V F : (E).Domain} (hW : Qval_d M B R z U w W) (hQ : Qval_d M B R z U A Q)
    (hV : Qval_d M B R z U T V) (hF : Qval_d M B R z U t F) : Chain_d J Q V Q W F := by
  obtain ⟨e, hv, he, hi⟩ := check_map_l O hZF hU hb
  have heW := qval_unique_l (hv ω w hw) hW
  obtain ⟨hgraph, hentry⟩ := nseq_value_l O hZF hU (hU.proper b hb).1 ht hF e hv
  have hfn : (E).IsSetFunction J F := by
    refine ⟨hgraph, fun x y v hxy hxv => ?_⟩
    obtain ⟨i, s, his, hix, hsy⟩ := (hentry x y).mp hxy
    obtain ⟨j, t, hjt, hjx, htv⟩ := (hentry x v).mp hxv
    have hij := hi (hix.trans hjx.symm)
    subst j
    have hst := hf.1.2 i s t his hjt
    subst t
    exact qval_unique_l hsy htv
  have domain : (E).IsDomainOf J W F := by
    intro x
    change (x ∈ W ↔ ∃ y, Entry_d E x y F)
    rw [← heW, he ω x]
    constructor
    · rintro ⟨i, hi, rfl⟩
      obtain ⟨s, his⟩ := (hf.2.1 i).mp hi
      obtain ⟨y, hy⟩ := name_value_l (R := R) (z := z) (U := U) (hf.2.2.1 i s his).1
      exact ⟨y, (hentry (e i) y).mpr ⟨i, s, his, rfl, hy⟩⟩
    · rintro ⟨y, hxy⟩
      obtain ⟨i, s, his, hix, _⟩ := (hentry x y).mp hxy
      exact ⟨i, (hf.2.1 i).mpr ⟨s, his⟩, hix⟩
  have mem {x y} (hxy : Entry_d E x y F) : y ∈ Q := by
    obtain ⟨i, s, his, _, hsy⟩ := (hentry x y).mp hxy
    exact (qval_mem_forcing_l O hZF hU hsy hQ).mp ⟨p, hp, (hf.2.2.1 i s his).2⟩
  refine ⟨⟨hfn, domain, fun x hx => ?_⟩, fun x y hxy hy => ?_, fun x y a c hxy hxa hyc => ?_⟩
  · obtain ⟨y, hxy⟩ := (domain x).mp hx
    exact ⟨y, mem hxy, hxy⟩
  · exact KP.mem_irrefl_d (ZF.modelsKP (preserves_zf_l O hZF hU)) Q (hy ▸ mem hxy)
  · obtain ⟨i, s, his, rfl, hsa⟩ := (hentry x a).mp hxa
    obtain ⟨j, t, hjt, rfl, htc⟩ := (hentry y c).mp hyc
    exact (rel_force_truth_l O hZF hU htc hsa hV).mp
      ⟨p, hp, hf.2.2.2 i j s t ((image_member_l e hi he).mp hxy.predecessor_mem) his hjt⟩

omit hU in
include O in
/-- 有限参数反射将实际逐项证书合成为同一条件下的完整下降链力迫。 -/
theorem nchain_force_l {b p ω A T f t w} (hb : M.mem b B) (hp : Below_d M B R z p b)
    (hf : Nchain_d I B R z p ω A T f) (ht : Nseq_d M B b f t) (hw : Check_d M b ω w)
    (hA : Name_d M B A) (hT : Name_d M B T) :
    Forces_d M B R z (chain_m (.bound 2) (.bound 1) (.bound 2) (.bound 3) .newest)
      ((((⟨fun _ => w, fun _ => w⟩ : Env M 1).push A).push T).push t) p := by
  let ρ₀ : Env M 4 := (((⟨fun _ => B, fun _ => B⟩ : Env M 1).push R).push z).push b
  let ρ : Env M 11 := ((((((ρ₀.push ω).push A).push T).push f).push w).push t).push p
  let φ : Formula 1 4 := chain_m (.bound 2) (.bound 1) (.bound 2) (.bound 3) .newest
  let e : Fin 4 → Term 11 := Fin.cases (.bound 1) (Fin.cases (.bound 4) (Fin.cases (.bound 5) (fun _ => .bound 2)))
  let α : Formula 1 11 := .conj (.mem (.bound 7) (.bound 10))
    (.conj (below_m (.bound 10) (.bound 9) (.bound 8) .newest (.bound 7))
      (.conj (check_m (.bound 7) (.bound 6) (.bound 2))
        (.conj (nseq_m (.bound 10) (.bound 7) (.bound 3) (.bound 1))
          (nchain_m (.bound 10) (.bound 9) (.bound 8) .newest (.bound 6) (.bound 5) (.bound 4) (.bound 3)))))
  have hφ : φ.FreeClosed := chain_m_freeClosed _ _ _ _ _ rfl rfl rfl rfl rfl
  have hα : α.FreeClosed := by simp -implicitDefEqProofs [α, Definitional.Formula.FreeClosed]
  have raw (N : SetTheory.Structure.{u}) (hN : N.Models ZF) (η : Env N 11) : Formula.satisfies η α ↔
      N.mem (η.bound 7) (η.bound 10) ∧ Below_d N (η.bound 10) (η.bound 9) (η.bound 8) (η.bound 0) (η.bound 7) ∧
      Check_d N (η.bound 7) (η.bound 6) (η.bound 2) ∧ Nseq_d N (η.bound 10) (η.bound 7) (η.bound 3) (η.bound 1) ∧
      Nchain_d (kpair_interpretation_l N hN.1 (KP.exists_pair (ZF.modelsKP hN)))
        (η.bound 10) (η.bound 9) (η.bound 8) (η.bound 0) (η.bound 6) (η.bound 5) (η.bound 4) (η.bound 3) := by
    simp only [α, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff, below_sat_l N hN.1,
      check_sat_l N hN.1, nseq_sat_l N hN.1,
      nchain_sat_l (kpair_interpretation_l N hN.1 (KP.exists_pair (ZF.modelsKP hN))) hN.1]
    rfl
  have hn : ∀ i, Name_d M B ((e i).eval ρ) := Fin.cases ht.1 (Fin.cases hT
    (Fin.cases hA (fun _ => check_name_l M (check_range_l M hZF) hb hw)))
  have hh := forces_of_generics_l φ hφ α hα e (.bound 10) (.bound 9) (.bound 8) .newest
    (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl)))) rfl rfl rfl rfl
    (fun N hN η L _ _ _ ha U hU hpU ξ hξ => ?_) hZF ρ O hn hp.1 hp.2.1
      ((raw M hZF ρ).mpr ⟨hb, hp, hw, ht, hf⟩)
  · exact (forces_env_l hZF.1 φ hφ _ _
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl)))) p).mp hh
  · obtain ⟨hb', hp', hw', ht', hf'⟩ := (raw N hN η).mp ha
    have hbU := hU.upward _ _ hpU hb' hp'.2.2
    exact (chain_sat_l (kpair_interpretation_l _ (extension_ext_l L hN hU) (internal_pair_l L hN hU))
      (extension_ext_l L hN hU) ξ _ _ _ _ _).mpr
      (nchain_value_l L hN hU hbU hpU hf' ht' hw' (hξ 3) (hξ 2) (hξ 1) (hξ 0))

end YesMetaZFC.Model.Forcing.Internal
