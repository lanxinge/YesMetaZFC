import YesMetaZFC.Model.SetTheory.Internal.TruthRules

/-! # 内部公式码的实际全集

完整公式码为 (程序,根行号)。程序是 ω×(ω×(ω×ω)) 的内部子集，根编号属于 ω；
在这一幂集乘积界上按合法性分离，得到包含全部内部有限公式的实际集合。
-/

namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Sformula_d (ω a n F k : M.Domain) : Prop :=
  I.Codes a F k ∧ Sfm_d I ω n F ∧ M.mem k n

def sformula_m {n} (ω a l F k : Term n) : Formula 1 n :=
  .conj (𝒞.code a F k) (.conj (sfm_m (𝒞 := 𝒞) ω l F) (.mem k l))
derive_free_closed sformula_m

theorem sformula_sat_l (hE : Extensional M) {n} (ρ : Env M n) (ω a l F k : Term n) :
    Formula.satisfies ρ (sformula_m (𝒞 := 𝒞) ω a l F k) ↔
      Sformula_d I (ω.eval ρ) (a.eval ρ) (l.eval ρ) (F.eval ρ) (k.eval ρ) := by
  simp only [sformula_m, Sformula_d, Formula.satisfies_conj_iff, I.satisfies_code_iff,
    sfm_sat_l I hE, Formula.satisfies_mem_iff]

theorem sformula_unique_l (hE : Extensional M) {ω a n F k m G j}
    (h : Sformula_d I ω a n F k) (g : Sformula_d I ω a m G j) : n = m ∧ F = G ∧ k = j := by
  obtain ⟨he, hk⟩ := I.injective h.1 g.1
  subst G
  exact ⟨h.2.1.2.1.length_eq hE g.2.1.2.1, rfl, hk⟩

def Scode_d (ω C : M.Domain) : Prop := ∀ a, M.mem a C ↔ ∃ n F k, Sformula_d I ω a n F k

def scode_m {n} (ω C : Term n) : Formula 1 n :=
  .forallE (.iff (.mem .newest C.weaken) (.existsE (.existsE (.existsE
    (sformula_m (𝒞 := 𝒞) ω.weaken.weaken.weaken.weaken (.bound 3) (.bound 2) (.bound 1) .newest)))))
derive_free_closed scode_m

theorem scode_sat_l (hE : Extensional M) {n} (ρ : Env M n) (ω C : Term n) :
    Formula.satisfies ρ (scode_m (𝒞 := 𝒞) ω C) ↔ Scode_d I (ω.eval ρ) (C.eval ρ) := by
  simp only [scode_m, Scode_d, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_exists_iff, sformula_sat_l I hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

/-- 合法指令全部落在同一个可数的三重自然数积中。 -/
theorem sfm_node_mem_l (hZF : M.Models ZF) {ω P Q r c} (hω : M.IsOmega ω)
    (hP : M.IsCartesianProduct I P ω ω) (hQ : M.IsCartesianProduct I Q ω P)
    (hr : M.mem r ω) (hc : Sfm_node_d I ω r c) : M.mem c Q := by
  have op {k i j} (h : Sop_d I k c i j) (hi : M.mem i ω) (hj : M.mem j ω) : M.mem c Q := by
    obtain ⟨a, o, ho, ha, hc⟩ := h
    exact (hQ c).mpr ⟨o, num_mem_l hZF.1 hω ho, a, (hP a).mpr ⟨i, hi, j, hj, ha⟩, hc⟩
  rcases hc with ⟨i, j, hs, hi, hj⟩ | ⟨i, j, hs, hi, hj⟩ | ⟨i, j, hs, hi, hj⟩ | ⟨i, j, hs, hi, hj⟩
  · exact op hs hi hj
  · exact op hs hi hj
  · exact op hs (hω.transitive hZF r hr i hi) (hω.transitive hZF r hr j hj)
  · exact op hs hi (hω.transitive hZF r hr j hj)

/-- 全部内部有限公式码组成一个模型内集合，而非仅有外部标准公式的枚举。 -/
theorem scode_exists_l (hZF : M.Models ZF) {ω} (hω : M.IsOmega ω) : ∃ C, Scode_d I ω C := by
  obtain ⟨P, hP⟩ := ZF.exists_cartesianProduct hZF I ω ω
  obtain ⟨Q, hQ⟩ := ZF.exists_cartesianProduct hZF I ω P
  obtain ⟨D, hD⟩ := ZF.exists_cartesianProduct hZF I ω Q
  obtain ⟨U, hU⟩ := ZF.exists_powerSet hZF D
  obtain ⟨A, hA⟩ := ZF.exists_cartesianProduct hZF I U ω
  have bound {a n F k} (ha : Sformula_d I ω a n F k) : M.mem a A := by
    obtain ⟨hc, hF, hk⟩ := ha
    have row r (hr : M.mem r n) := hω.transitive hZF n hF.1 r hr
    refine (hA a).mpr ⟨F, (hU F).mpr ?_, k, row k hk, hc⟩
    intro p hp
    obtain ⟨r, c, hpc⟩ := hF.2.1.2.1.1 p hp
    have hrc : M.PairMember I r c F := ⟨p, hpc, hp⟩
    exact (hD p).mpr ⟨r, row r ((hF.2.1.2.2 r).mpr ⟨c, hrc⟩), c,
      sfm_node_mem_l I hZF hω hP hQ (row r ((hF.2.1.2.2 r).mpr ⟨c, hrc⟩)) (hF.2.2 r c hrc), hpc⟩
  let ρ : Env M 1 := ⟨fun _ => ω, fun _ => ω⟩
  let φ : UnarySchema 1 := { body := .existsE (.existsE (.existsE
    (sformula_m (𝒞 := 𝒞) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest))) }
  have hφ a : φ.denote ρ a ↔ ∃ n F k, Sformula_d I ω a n F k := by
    simp only [UnarySchema.denote, φ, Formula.satisfies_exists_iff, sformula_sat_l I hZF.1]
    rfl
  obtain ⟨C, hC⟩ := ZF.separation_exists_d hZF φ ρ A
  refine ⟨C, fun a => (hC a).trans ?_⟩
  rw [show Formula.satisfies (ρ.push a) φ.body ↔ _ from hφ a]
  exact ⟨And.right, fun h => ⟨h.elim fun n h => h.elim fun F h => h.elim fun k h => bound h, h⟩⟩

theorem scode_unique_l (hE : Extensional M) {ω C D} (hC : Scode_d I ω C) (hD : Scode_d I ω D) : C = D :=
  hE.eq_of_same_members C D (fun a => (hC a).trans (hD a).symm)

/-- 任意变量对的关系原子有实际公式码，作为编码语言的直接构造实例。 -/
theorem sformula_rel_l (hZF : M.Models ZF) {ω i j} (hω : M.IsOmega ω)
    (hi : M.mem i ω) (hj : M.mem j ω) : ∃ a n F k c,
    Sformula_d I ω a n F k ∧ M.PairMember I k c F ∧ Sop_d I 0 c i j := by
  obtain ⟨e, he⟩ := KP.exists_empty (ZF.modelsKP hZF)
  have hF : Sfm_d I ω e e := ⟨num_mem_l hZF.1 hω (show Num_d 0 e from he),
    Structure.IsSequenceOfLength.empty I he, fun _ _ h => h.elim fun p hp => (he p hp.2).elim⟩
  obtain ⟨c, hc⟩ := sop_exists_l I (ZF.modelsKP hZF) 0 i j
  obtain ⟨n, F, hn, hf, hd⟩ := sfm_append_l I hZF hω hF (Or.inl ⟨i, j, hc, hi, hj⟩)
  obtain ⟨a, ha⟩ := I.total F e
  exact ⟨a, n, F, e, c, ⟨ha, hf, hn.predecessor_mem⟩, (hd e c).mpr (Or.inr ⟨rfl, rfl⟩), hc⟩

end YesMetaZFC.SetTheory.Internal
