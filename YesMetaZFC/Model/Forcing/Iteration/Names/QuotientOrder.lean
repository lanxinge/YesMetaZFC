import YesMetaZFC.Model.Forcing.Iteration.Names.Quotient
import YesMetaZFC.Model.Forcing.Iteration.Names.GenericName

/-! # 任意阶段商名称的实际尾部加强

在每个决定旧条件的前缀分支上，换入该前缀后得到字面的旧序加强。
规范拼接的最大下界性质把这种比较传给所有后续加强，进而得到泛型接受力迫。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}}

def Row_quot_lower_d (I : kpair_convention_l.Interpretation M) (α B R b D V N τ p q : M.Domain) : Prop :=
  ∀ r a v c, Row_dec_d I α B R b D N τ c r a v → Below_d M B R B c p →
    ∀ w, Row_splice_d M α c q w → Entry_d M w r V

def row_quot_lower_m {n} (α B R b D V N τ p q : Term n) : Formula 1 n :=
  .forallE (.forallE (.forallE (.forallE
    (.imp (row_dec_m α.weaken.weaken.weaken.weaken B.weaken.weaken.weaken.weaken
      R.weaken.weaken.weaken.weaken b.weaken.weaken.weaken.weaken D.weaken.weaken.weaken.weaken
      N.weaken.weaken.weaken.weaken τ.weaken.weaken.weaken.weaken .newest (.bound 3) (.bound 2) (.bound 1))
      (.imp (below_m B.weaken.weaken.weaken.weaken R.weaken.weaken.weaken.weaken
        B.weaken.weaken.weaken.weaken .newest p.weaken.weaken.weaken.weaken)
        (.forallE (.imp (row_splice_m α.weaken.weaken.weaken.weaken.weaken (.bound 1)
          q.weaken.weaken.weaken.weaken.weaken .newest)
          (entry_m .newest (.bound 4) V.weaken.weaken.weaken.weaken.weaken))))))))
derive_free_closed row_quot_lower_m

theorem row_quot_lower_sat_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M) {n}
    (ρ : Env M n) (α B R b D V N τ p q : Term n) : Formula.satisfies ρ (row_quot_lower_m α B R b D V N τ p q) ↔
      Row_quot_lower_d I (α.eval ρ) (B.eval ρ) (R.eval ρ) (b.eval ρ) (D.eval ρ) (V.eval ρ)
        (N.eval ρ) (τ.eval ρ) (p.eval ρ) (q.eval ρ) := by
  simp only [row_quot_lower_m, Row_quot_lower_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    row_dec_sat_l I hE, below_sat_l M hE, row_splice_sat_l M hE, entry_sat_l M hE, Definitional.Term.eval_weaken]
  rfl

/-- 任意阶段的实际尾部加强迫使旧条件名称被泛型接受；无需分离性或额外融合假设。 -/
theorem row_quot_accept_l (hZF : M.Models ZF) {α B R b D V N τ p q K γ}
    (O : Cond_order_d M B R B) (L : Cond_order_d M D V D)
    (k : Row_link_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) α B R D V)
    (hτ : Name_d M B τ) (hq : M.mem q D)
    (hpq : M.IsRestrictionOf (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) p q α)
    (hK : Row_quot_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) α B b D N K)
    (hτK : Mem_force_d M B R B p τ K) (hγ : Gname_d (M := M) D b γ)
    (hl : Row_quot_lower_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) α B R b D V N τ p q) :
    Mem_force_d M D V D q τ γ := by
  have hp := hτK.1
  refine ⟨hq, fun r hr => ?_⟩
  obtain ⟨a, ha, har⟩ := k.restrict r hr.1
  have hap : Below_d M B R B a p := ⟨ha, (fun he => KP.mem_irrefl_d (ZF.modelsKP hZF) B (he ▸ ha)),
    k.mono r q a p hr.1 hq har hpq hr.2.2⟩
  obtain ⟨c, hca, r₀, a₀, v, hc⟩ := row_quot_decide_l hK hτK a hap
  have hcp := below_trans_l O hp hca hap
  obtain ⟨q', hq'⟩ := row_splice_exists_l M hZF α c q
  obtain ⟨hq'D, _, _⟩ := k.splice q p c q' hq hpq hca.1 hcp.2.2 hq'
  have hq'r := hl r₀ a₀ v c hc hcp q' hq'
  obtain ⟨hr₀, hr₀N, ha₀, har₀, hrv, _, heq⟩ := hc
  obtain ⟨w, hw⟩ := row_splice_exists_l M hZF α c r
  obtain ⟨hwD, hwr, hwc⟩ := k.splice r a c w hr.1 har hca.1 hca.2.2 hw
  have hwq := L.trans w r q hwD hr.1 hq hwr hr.2.2
  have hwq' := k.splice_glb q p c q' w hq hpq hca.1 hcp.2.2 hq' hwD hwq hwc
  have hwr₀ := L.trans w q' r₀ hwD hq'D hr₀ hwq' hq'r
  have hvK := (hK.2 v a₀).mpr ⟨ha₀, r₀, hr₀, hr₀N, har₀, hrv⟩
  have hv := (name_entry_l M hK.1 hvK).1
  have hwz : w ≠ D := fun he => KP.mem_irrefl_d (ZF.modelsKP hZF) D (he ▸ hwD)
  exact ⟨w, v, r₀, ⟨hwD, hwz, hwr⟩, (hγ.2 v r₀).mpr ⟨hr₀, hrv⟩, hwr₀,
    eq_force_lower_l L hZF (row_name_l k hτ) (row_name_l k hv) c w (k.mem c hca.1) ⟨hwD, hwz, hwc⟩
      ((row_eq_force_l hZF O L k hca.1 hτ hv).mp heq)⟩

end YesMetaZFC.Model.Forcing.Internal
