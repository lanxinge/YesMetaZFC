import YesMetaZFC.SetTheory.Descriptive.Borel.Pullback
import YesMetaZFC.SetTheory.Descriptive.ContinuousLift
import YesMetaZFC.SetTheory.Descriptive.Projective.Quantifier

/-! # 任意内部射影层的统一连续逆像码

在 B^B 中迭代 f↦f×id，再对原 Borel 矩阵作一次逆像替换。
该算法在每个内部层号都有唯一输出，故可逐项处理内部可数码族。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Lgraph_d (B J X L : M.Domain) : Prop := M.IsFunctionSpace I X B B ∧
  M.IsSetFunctionFromTo I L X X ∧ ∀ f g, M.PairMember I f g L ↔ M.mem f X ∧ Lift_d I B J f g
def lgraph_m {d} (B J X L : Term d) : Formula 1 d := .conj (Formula.isFunctionSpace 𝒞 X B B) (.conj
  (Formula.isFunctionFromTo 𝒞 L X X) (.forallE (.forallE (.iff
    (Formula.orderedPairMem 𝒞 (.bound 1) .newest L.weaken.weaken) (.conj (.mem (.bound 1) X.weaken.weaken)
      (lift_m (𝒞 := 𝒞) B.weaken.weaken J.weaken.weaken (.bound 1) .newest))))))
@[simp] theorem lgraph_closed_l {d} (B J X L : Term d) (hB : B.freeSupport = []) (hJ : J.freeSupport = [])
    (hX : X.freeSupport = []) (hL : L.freeSupport = []) : (lgraph_m (𝒞 := 𝒞) B J X L).FreeClosed := by
  simp -implicitDefEqProofs [lgraph_m, Formula.isFunctionSpace, Definitional.Formula.FreeClosed, hB, hJ, hX, hL]
theorem lgraph_sat_l (hE : Extensional M) {d} (ρ : Env M d) (B J X L : Term d) :
    Formula.satisfies ρ (lgraph_m (𝒞 := 𝒞) B J X L) ↔ Lgraph_d I (B.eval ρ) (J.eval ρ) (X.eval ρ) (L.eval ρ) := by
  simp only [lgraph_m, Lgraph_d, Formula.satisfies_conj_iff, Formula.satisfies_isFunctionSpace_iff I hE,
    Formula.satisfies_isFunctionFromTo_iff I hE, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_orderedPairMem_iff I, Formula.satisfies_mem_iff, lift_sat_l I hE, Definitional.Term.eval_weaken]; rfl

theorem lgraph_exists_l (hZF : M.Models ZF) {ω B J} (hB : Baire_d I ω B) (hJ : Npair_d I ω J) :
    ∃ X L, Lgraph_d I B J X L := by
  obtain ⟨X, hX⟩ := ZF.exists_functionSpace hZF I B B
  let ρ : Env M 2 := (⟨fun _ => B, fun _ => B⟩ : Env M 1).push J
  let φ : BinarySchema 2 := { body := lift_m (𝒞 := 𝒞) (.bound 3) (.bound 2) (.bound 1) .newest }
  have hp f g : φ.denote ρ f g ↔ Lift_d I B J f g := lift_sat_l I hZF.1 _ _ _ _ _
  obtain ⟨L, hL, hl⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := X) (target := X)
    (fun f hf => (lift_exists_l I hZF hB hJ ((hX f).mp hf)).imp fun g hg => (hp f g).mpr hg)
    (fun _ _ _ _ h k => lift_unique_l I hZF.1 ((hp _ _).mp h) ((hp _ _).mp k))
    (fun _ g _ h => (hX g).mpr ((hp _ _).mp h).1)
  exact ⟨X, L, hX, hL, fun f g => (hl f g).trans (and_congr_right fun _ => hp f g)⟩

theorem lift_iter_cont_l (hZF : M.Models ZF) {ω A B J X L f n g} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (hJ : Npair_d I ω J) (hL : Lgraph_d I B J X L)
    (hf : Cont_d I A B f) (h : Iv_d I ω X L f n g) : Cont_d I A B g := by
  obtain ⟨H, hH, hg⟩ := h
  let ρ : Env M 3 := ((⟨fun _ => A, fun _ => A⟩ : Env M 1).push B).push H
  let φ : UnarySchema 3 := { body := .forallE (.imp (Formula.orderedPairMem 𝒞 (.bound 1) .newest (.bound 2))
    (cont_m (𝒞 := 𝒞) (.bound 4) (.bound 3) .newest)) }
  have hp n : φ.denote ρ n ↔ ∀ g, M.PairMember I n g H → Cont_d I A B g := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      Formula.satisfies_orderedPairMem_iff I, cont_sat_l I hZF.1]; rfl
  have all : ∀ n, M.mem n ω → ∀ g, M.PairMember I n g H → Cont_d I A B g := by
    apply hB.1.induction
    · obtain ⟨C, hC⟩ := ZF.separation_exists_d hZF φ ρ ω
      exact ⟨C, fun n => (hC n).trans (and_congr_right fun _ => hp n)⟩
    · intro z hz g hg
      exact hH.1.1.2 z f g (hH.2.1 z hz) hg ▸ hf
    · intro n hn ih m hm g hg
      obtain ⟨f', _, hf'⟩ := hH.1.2.2 n hn
      exact lift_cont_l I hZF hB hA hJ (ih f' hf') ((hL.2.2 f' g).mp (hH.2.2 n m f' g hm hf' hg)).2
  exact all n (hH.1.input_mem_of_pairMember hg) g hg

theorem pval_pull_l (hZF : M.Models ZF) {ω A B J X L} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (hJ : Npair_d I ω J) (hL : Lgraph_d I B J X L) :
    ∀ n, M.mem n ω → ∀ f g C D K V, Cont_d I A B f → Iv_d I ω X L f n g →
      Ip_d I B g C D → Pval_d I ω B J n C K → Pval_d I ω B J n D V → Ip_d I B f K V := by
  let ρ : Env M 6 := (((((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push A).push B).push J).push X).push L
  let φ : UnarySchema 6 := { body := .forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.imp
    (cont_m (𝒞 := 𝒞) (.bound 11) (.bound 10) (.bound 5)) (.imp
    (iv_m (𝒞 := 𝒞) (.bound 12) (.bound 8) (.bound 7) (.bound 5) (.bound 6) (.bound 4)) (.imp
    (ip_m (𝒞 := 𝒞) (.bound 10) (.bound 4) (.bound 3) (.bound 2)) (.imp
    (pval_m (𝒞 := 𝒞) (.bound 12) (.bound 10) (.bound 9) (.bound 6) (.bound 3) (.bound 1)) (.imp
    (pval_m (𝒞 := 𝒞) (.bound 12) (.bound 10) (.bound 9) (.bound 6) (.bound 2) .newest)
    (ip_m (𝒞 := 𝒞) (.bound 10) (.bound 5) (.bound 1) .newest))))))))))) }
  have hp n : φ.denote ρ n ↔ ∀ f g C D K V, Cont_d I A B f → Iv_d I ω X L f n g →
      Ip_d I B g C D → Pval_d I ω B J n C K → Pval_d I ω B J n D V → Ip_d I B f K V := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      cont_sat_l I hZF.1, iv_sat_l I hZF.1, ip_sat_l I, pval_sat_l I hZF.1]; rfl
  apply hB.1.induction
  · obtain ⟨T, hT⟩ := ZF.separation_exists_d hZF φ ρ ω
    exact ⟨T, fun n => (hT n).trans (and_congr_right fun _ => hp n)⟩
  · intro z hz f g C D K V hf hg hip hK hV
    have e := (iv_zero_l I hZF hB.1 hL.2.1 ((hL.1 f).mpr hf.1) hz).mp hg
    subst g
    obtain ⟨H, hH, hk⟩ := hK
    obtain ⟨G, hG, hv⟩ := hV
    exact hH.fn.2 z C K (hH.zero z hz) hk ▸ hG.fn.2 z D V (hG.zero z hz) hv ▸ hip
  · intro n hn ih m hm f g C D K V hf hg hip hK hV
    obtain ⟨f', _, hf'⟩ := hL.2.1.2.2 f ((hL.1 f).mpr hf.1)
    have hl := ((hL.2.2 f f').mp hf').2
    have hg' := (iv_shift_l I hZF hB.1 hL.2.1 hn hm hf').mp hg
    obtain ⟨K', hk, hK⟩ := (pval_succ_l I hZF hB.1 hn hm).mp hK
    obtain ⟨V', hv, hV⟩ := (pval_succ_l I hZF hB.1 hn hm).mp hV
    exact lift_step_l I hZF hB hJ hf.1 hl
      (ih f' g C D K' V' (lift_cont_l I hZF hB hA hJ hf hl) hg' hip hk hv) hK hV

def Ppull_d (ω A E X L f n c d : M.Domain) : Prop := ∃ g, Iv_d I ω X L f n g ∧ Bpull_d I ω A E g c d
def ppull_m {d} (ω A E X L f n c e : Term d) : Formula 1 d := .existsE (.conj
  (iv_m (𝒞 := 𝒞) ω.weaken X.weaken L.weaken f.weaken n.weaken .newest)
  (bpull_m (𝒞 := 𝒞) ω.weaken A.weaken E.weaken .newest c.weaken e.weaken))
derive_free_closed ppull_m
theorem ppull_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω A E X L f n c e : Term d) :
    Formula.satisfies ρ (ppull_m (𝒞 := 𝒞) ω A E X L f n c e) ↔
      Ppull_d I (ω.eval ρ) (A.eval ρ) (E.eval ρ) (X.eval ρ) (L.eval ρ) (f.eval ρ) (n.eval ρ) (c.eval ρ) (e.eval ρ) := by
  simp only [ppull_m, Ppull_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    iv_sat_l I hE, bpull_sat_l I hE, Definitional.Term.eval_weaken]; rfl

theorem ppull_unique_l (hZF : M.Models ZF) {ω A E X L f n c d e} (hω : M.IsOmega ω)
    (hL : M.IsSetFunction I L) (h : Ppull_d I ω A E X L f n c d) (k : Ppull_d I ω A E X L f n c e) : d = e := by
  obtain ⟨g, hg, hd⟩ := h
  obtain ⟨g', hg', he⟩ := k
  exact bpull_unique_l I hZF.1 hd (iv_unique_l I hZF hω hL hg' hg ▸ he)

theorem ppull_exists_l (hZF : M.Models ZF) {ω A B J E X L f n c} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (he : M.IsSetInjectionFromTo I E A ω) (hL : Lgraph_d I B J X L)
    (hf : M.IsSetFunctionFromTo I f B B) (hn : M.mem n ω) (hc : Bcode_d I ω A A c) :
    ∃ d, Ppull_d I ω A E X L f n c d ∧ Bcode_d I ω A A d := by
  obtain ⟨g, hg⟩ := iv_exists_l I hZF hB.1 hL.2.1 ((hL.1 f).mpr hf) hn
  obtain ⟨d, hd, hd'⟩ := bpull_exists_l I hZF hB.1 hA he hc
  exact ⟨d, ⟨g, hg, hd⟩, hd'⟩

theorem ppull_value_l (hZF : M.Models ZF) {ω A B J E X L f n c d C D K V} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (hJ : Npair_d I ω J) (he : M.IsSetInjectionFromTo I E A ω)
    (hL : Lgraph_d I B J X L) (hf : Cont_d I A B f) (hn : M.mem n ω) (hc : Bcode_d I ω A A c)
    (h : Ppull_d I ω A E X L f n c d) (hC : Bden_d I ω A A B c C) (hD : Bden_d I ω A A B d D)
    (hK : Pval_d I ω B J n C K) (hV : Pval_d I ω B J n D V) : Ip_d I B f K V := by
  obtain ⟨g, hg, hd⟩ := h
  have hgc := lift_iter_cont_l I hZF hB hA hJ hL hf hg
  have hip : Ip_d I B g C D := by
    intro x
    refine (hD x).trans (and_congr_right fun hx => ⟨?_, ?_⟩)
    · intro hd'
      obtain ⟨y, hy, hxy⟩ := hgc.1.2.2 x hx
      exact ⟨y, hxy, (hC y).mpr ⟨hy, (bpull_correct_l I hZF hB.1 hA he hgc hc hd x y hxy).mp hd'⟩⟩
    · rintro ⟨y, hxy, hy⟩
      exact (bpull_correct_l I hZF hB.1 hA he hgc hc hd x y hxy).mpr ((hC y).mp hy).2
  exact pval_pull_l I hZF hB hA hJ hL n hn f g C D K V hf hg hip hK hV

end YesMetaZFC.SetTheory.Descriptive
