import YesMetaZFC.Model.SetTheory.Internal.Satisfaction
import YesMetaZFC.SetTheory.Card.Basic

/-! # 带集合谓词的内部初等嵌入

在无自隶属的集合载体上，用 R(x,y) ↔ x∈y ∨ (x=y ∧ x∈A)
编码 (X,∈,A)。对角线恢复 A，非对角线恢复 ∈；统一满足关系仍使用原内部公式码。
嵌入、赋值及其复合均为模型内集合，初等性量化包括非标准码在内的全部内部公式。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Spred_d (c X A R : M.Domain) : Prop := Smdl_d I c X R ∧ M.MemberSubset A X ∧
  ∀ x y, M.PairMember I x y R ↔ M.mem x X ∧ M.mem y X ∧ (M.mem x y ∨ x = y ∧ M.mem x A)

def spred_m {n} (c X A R : Term n) : Formula 1 n :=
  .conj (smdl_m (𝒞 := 𝒞) c X R) (.conj (Formula.subset A X)
    (.forallE (.forallE (.iff (Formula.orderedPairMem 𝒞 (.bound 1) .newest R.weaken.weaken)
      (.conj (.mem (.bound 1) X.weaken.weaken) (.conj (.mem .newest X.weaken.weaken)
        (.disj (.mem (.bound 1) .newest) (.conj (Formula.extensionalEq (.bound 1) .newest)
          (.mem (.bound 1) A.weaken.weaken)))))))))
derive_free_closed spred_m

theorem spred_sat_l (hE : Extensional M) {n} (ρ : Env M n) (c X A R : Term n) :
    Formula.satisfies ρ (spred_m (𝒞 := 𝒞) c X A R) ↔ Spred_d I (c.eval ρ) (X.eval ρ) (A.eval ρ) (R.eval ρ) := by
  simp only [spred_m, Spred_d, Formula.satisfies_conj_iff, smdl_sat_l I, Formula.satisfies_subset_iff,
    Formula.satisfies_forall_iff, Formula.satisfies_iff_iff, Formula.satisfies_orderedPairMem_iff I,
    Formula.satisfies_mem_iff, Formula.satisfies_disj_iff, Formula.satisfies_extensionalEq_iff_eq hE,
    Definitional.Term.eval_weaken]
  rfl

/-- 每个实际集合谓词都生成结构码；不要求它可由载体内部公式定义。 -/
theorem spred_exists_l (hZF : M.Models ZF) {X A} (hX : ∃ x, M.mem x X) (hA : M.MemberSubset A X) :
    ∃ c R, Spred_d I c X A R := by
  let φ : BinarySchema 1 := {
    body := .disj (.mem (.bound 1) .newest)
      (.conj (Formula.extensionalEq (.bound 1) .newest) (.mem (.bound 1) (.bound 2))) }
  obtain ⟨c, R, hc, hr⟩ := smdl_exists_l I hZF φ ⟨fun _ => A, fun _ => A⟩ hX
  refine ⟨c, R, hc, hA, fun x y => (hr x y).trans (and_congr_right fun _ => and_congr_right fun _ => ?_)⟩
  simp only [φ, BinarySchema.denote, Formula.satisfies_disj_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_conj_iff, Formula.satisfies_extensionalEq_iff_eq hZF.1]
  rfl

/-- 编码的两个原子可精确还原，因此没有改变 (∈,A) 的数学内容。 -/
theorem spred_read_l (hKP : M.Models KP) {c X A R} (h : Spred_d I c X A R) (x y : M.Domain) :
    (M.PairMember I x x R ↔ M.mem x A) ∧
      (M.PairMember I x y R ∧ x ≠ y ↔ M.mem x X ∧ M.mem y X ∧ M.mem x y) := by
  constructor
  · rw [h.2.2 x x]
    exact ⟨fun hx => hx.2.2.elim (fun h => (KP.mem_irrefl_d hKP x h).elim) And.right,
      fun hx => ⟨h.2.1 x hx, h.2.1 x hx, Or.inr ⟨rfl, hx⟩⟩⟩
  · rw [h.2.2 x y]
    exact ⟨fun ⟨hx, hn⟩ => ⟨hx.1, hx.2.1, hx.2.2.elim id (fun h => (hn h.1).elim)⟩,
      fun ⟨hx, hy, hm⟩ => ⟨⟨hx, hy, Or.inl hm⟩, fun he => KP.mem_irrefl_d hKP y (he ▸ hm)⟩⟩

def Smap_assign_d (ω j f g : M.Domain) : Prop := ∀ n, M.mem n ω → ∀ x y,
  M.PairMember I n x f → M.PairMember I x y j → M.PairMember I n y g

def smap_assign_m {d} (ω j f g : Term d) : Formula 1 d := Formula.forallMem ω
  (.forallE (.forallE (.imp (Formula.orderedPairMem 𝒞 (.bound 2) (.bound 1) f.weaken.weaken.weaken)
    (.imp (Formula.orderedPairMem 𝒞 (.bound 1) .newest j.weaken.weaken.weaken)
      (Formula.orderedPairMem 𝒞 (.bound 2) .newest g.weaken.weaken.weaken)))))
derive_free_closed smap_assign_m

theorem smap_assign_sat_l {d} (ρ : Env M d) (ω j f g : Term d) :
    Formula.satisfies ρ (smap_assign_m (𝒞 := 𝒞) ω j f g) ↔
      Smap_assign_d I (ω.eval ρ) (j.eval ρ) (f.eval ρ) (g.eval ρ) := by
  simp only [smap_assign_m, Smap_assign_d, Formula.satisfies_forallMem_iff, Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff, Formula.satisfies_orderedPairMem_iff I, Definitional.Term.eval_weaken]
  rfl

theorem smap_assign_exists_l (hZF : M.Models ZF) {ω X Y j f}
    (hj : M.IsSetFunctionFromTo I j X Y) (hf : M.IsSetFunctionFromTo I f ω X) :
    ∃ g, M.IsSetFunctionFromTo I g ω Y ∧ Smap_assign_d I ω j f g := by
  obtain ⟨g, hg, he⟩ := ZF.exists_compositionFunction hZF I hf hj
  exact ⟨g, hg, fun n hn x y hx hy => (he n y).mpr ⟨hn, x, hx, hy⟩⟩

def Smap_d (ω c d X Y j : M.Domain) : Prop := M.IsSetInjectionFromTo I j X Y ∧
  ∃ C, Scode_d I ω C ∧ ∀ a f g, M.mem a C → M.IsSetFunctionFromTo I f ω X →
    M.IsSetFunctionFromTo I g ω Y → Smap_assign_d I ω j f g →
      (Satisfies_d I ω c a f ↔ Satisfies_d I ω d a g)

def smap_m {n} (ω c d X Y j : Term n) : Formula 1 n :=
  .conj (Formula.isInjectionFromTo 𝒞 j X Y) (.existsE (.conj (scode_m (𝒞 := 𝒞) ω.weaken .newest)
    (Formula.forallMem .newest (.forallE (.forallE (.imp
      (Formula.isFunctionFromTo 𝒞 (.bound 1) ω.weaken.weaken.weaken.weaken X.weaken.weaken.weaken.weaken)
      (.imp (Formula.isFunctionFromTo 𝒞 .newest ω.weaken.weaken.weaken.weaken Y.weaken.weaken.weaken.weaken)
        (.imp (smap_assign_m (𝒞 := 𝒞) ω.weaken.weaken.weaken.weaken j.weaken.weaken.weaken.weaken (.bound 1) .newest)
          (.iff (satisfies_m (𝒞 := 𝒞) ω.weaken.weaken.weaken.weaken c.weaken.weaken.weaken.weaken (.bound 2) (.bound 1))
            (satisfies_m (𝒞 := 𝒞) ω.weaken.weaken.weaken.weaken d.weaken.weaken.weaken.weaken (.bound 2) .newest))))))))))
derive_free_closed smap_m

theorem smap_sat_l (hE : Extensional M) {n} (ρ : Env M n) (ω c d X Y j : Term n) :
    Formula.satisfies ρ (smap_m (𝒞 := 𝒞) ω c d X Y j) ↔
      Smap_d I (ω.eval ρ) (c.eval ρ) (d.eval ρ) (X.eval ρ) (Y.eval ρ) (j.eval ρ) := by
  simp only [smap_m, Smap_d, Formula.satisfies_conj_iff, Formula.satisfies_isInjectionFromTo_iff I hE,
    Formula.satisfies_exists_iff, scode_sat_l I hE, Formula.satisfies_forallMem_iff,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Formula.satisfies_isFunctionFromTo_iff I hE,
    smap_assign_sat_l I, Formula.satisfies_iff_iff, satisfies_sat_l I hE, Definitional.Term.eval_weaken]
  exact and_congr Iff.rfl (exists_congr fun C => and_congr Iff.rfl
    ⟨fun h a f g ha => h a ha f g, fun h a ha f g => h a f g ha⟩)

/-- 完整初等证书直接作用于任意合法内部程序行，无需调用者另打包公式码。 -/
theorem Smap_d.ssat_l (hE : Extensional M) {ω c d X R Y S E K j n F r f g}
    (h : Smap_d I ω c d X Y j) (hX : Smdl_d I c X R) (hY : Smdl_d I d Y S)
    (hF : Sfm_d I ω n F) (hr : M.mem r n) (hA : M.IsFunctionSpace I E ω X)
    (hB : M.IsFunctionSpace I K ω Y) (hf : M.mem f E) (hg : M.mem g K) (hfg : Smap_assign_d I ω j f g) :
    Ssat_d I X R E F n r f ↔ Ssat_d I Y S K F n r g := by
  obtain ⟨a, ha⟩ := I.total F r
  have hc : Sformula_d I ω a n F r := ⟨ha, hF, hr⟩
  obtain ⟨C, hC, hh⟩ := h.2
  exact (satisfies_decode_l I hE hX hc hA).symm.trans
    ((hh a f g ((hC a).mpr ⟨n, F, r, hc⟩) ((hA f).mp hf) ((hB g).mp hg) hfg).trans
      (satisfies_decode_l I hE hY hc hB))

def Spred_emb_d (ω X A Y B j : M.Domain) : Prop := ∃ c R d S,
  Spred_d I c X A R ∧ Spred_d I d Y B S ∧ Smap_d I ω c d X Y j

def spred_emb_m {n} (ω X A Y B j : Term n) : Formula 1 n :=
  .existsE (.existsE (.existsE (.existsE (.conj
    (spred_m (𝒞 := 𝒞) (.bound 3) X.weaken.weaken.weaken.weaken A.weaken.weaken.weaken.weaken (.bound 2)) (.conj
    (spred_m (𝒞 := 𝒞) (.bound 1) Y.weaken.weaken.weaken.weaken B.weaken.weaken.weaken.weaken .newest)
    (smap_m (𝒞 := 𝒞) ω.weaken.weaken.weaken.weaken (.bound 3) (.bound 1)
      X.weaken.weaken.weaken.weaken Y.weaken.weaken.weaken.weaken j.weaken.weaken.weaken.weaken))))))
derive_free_closed spred_emb_m

theorem spred_emb_sat_l (hE : Extensional M) {n} (ρ : Env M n) (ω X A Y B j : Term n) :
    Formula.satisfies ρ (spred_emb_m (𝒞 := 𝒞) ω X A Y B j) ↔
      Spred_emb_d I (ω.eval ρ) (X.eval ρ) (A.eval ρ) (Y.eval ρ) (B.eval ρ) (j.eval ρ) := by
  simp only [spred_emb_m, Spred_emb_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    spred_sat_l I hE, smap_sat_l I hE, Definitional.Term.eval_weaken]
  rfl

/-- 实际恒等图及其全内部初等性，同时保留逐点图方程。 -/
theorem smap_identity_l (hZF : M.Models ZF) {ω X c} (hω : M.IsOmega ω) :
    ∃ j, Smap_d I ω c c X X j ∧ ∀ x y, M.PairMember I x y j ↔ M.mem x X ∧ x = y := by
  let ρ : Env M 0 := ⟨Fin.elim0, fun _ => X⟩
  have hd x y := Formula.denote_identityValue_iff hZF.1 ρ x y
  obtain ⟨j, hj, hj'⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I BinarySchema.identityValue ρ
    (source := X) (target := X) (fun x _ => ⟨x, (hd x x).mpr rfl⟩)
    (fun x _ y z hy hz => ((hd x y).mp hy).symm.trans ((hd x z).mp hz))
    (fun x y hx hy => (hd x y).mp hy ▸ hx)
  have he x y : M.PairMember I x y j ↔ M.mem x X ∧ x = y :=
    (hj' x y).trans (and_congr_right fun _ => hd x y)
  have hi : M.IsSetInjectionFromTo I j X X := ⟨hj,
    fun x y z hx hy => ((he x z).mp hx).2.trans ((he y z).mp hy).2.symm⟩
  obtain ⟨C, hC⟩ := scode_exists_l I hZF hω
  refine ⟨j, ⟨hi, C, hC, fun a f g _ hf hg hh => ?_⟩, he⟩
  have eq : f = g := hf.1.1.eq_of_pairMember_iff hZF.1 hg.1.1 (fun n x => ⟨fun hx => ?_, fun hx => ?_⟩)
  · exact eq ▸ Iff.rfl
  · exact hh n (hf.input_mem_of_pairMember hx) x x hx ((he x x).mpr ⟨hf.output_mem_of_pairMember hx, rfl⟩)
  · obtain ⟨y, hy, hny⟩ := hf.2.2 n (hg.input_mem_of_pairMember hx)
    have hng := hh n (hg.input_mem_of_pairMember hx) y y hny ((he y y).mpr ⟨hy, rfl⟩)
    exact hg.1.2 n y x hng hx ▸ hny

/-- 恒等图给出每个实际带谓词集合结构的初等嵌入实例。 -/
theorem spred_identity_l (hZF : M.Models ZF) {ω X A} (hω : M.IsOmega ω)
    (hX : ∃ x, M.mem x X) (hA : M.MemberSubset A X) : ∃ j, Spred_emb_d I ω X A X A j := by
  obtain ⟨c, R, hc⟩ := spred_exists_l I hZF hX hA
  obtain ⟨j, hj, _⟩ := smap_identity_l I hZF (X := X) (c := c) hω
  exact ⟨j, c, R, c, R, hc, hc, hj⟩

end YesMetaZFC.SetTheory.Internal
