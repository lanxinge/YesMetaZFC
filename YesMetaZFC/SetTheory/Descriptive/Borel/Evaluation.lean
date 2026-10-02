import YesMetaZFC.SetTheory.Descriptive.Borel.Code

/-! # Borel 码的内部求值与集合解释

固定空间点后，叶值与并节点由原公式分离得到，随后调用内部良基布尔递归。
每个合法码在每个内部点上有唯一的整树求值；根真值再分离出该码表示的实际集合。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Blit_d (F x a : M.Domain) : Prop := ∃ s, M.PairMember I a s F ∧ M.MemberSubset s x
def blit_m {d} (F x a : Term d) : Formula 1 d := .existsE
  (.conj (Formula.orderedPairMem 𝒞 a.weaken .newest F.weaken) (Formula.subset .newest x.weaken))
derive_free_closed blit_m
theorem blit_sat_l {d} (ρ : Env M d) (F x a : Term d) :
    Formula.satisfies ρ (blit_m (𝒞 := 𝒞) F x a) ↔ Blit_d I (F.eval ρ) (x.eval ρ) (a.eval ρ) := by
  simp only [blit_m, Blit_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_orderedPairMem_iff I, Formula.satisfies_subset_iff, Definitional.Term.eval_weaken]; rfl

def Buni_d (N F a : M.Domain) : Prop := ¬ M.mem a N ∧ ¬ ∃ s, M.PairMember I a s F
def buni_m {d} (N F a : Term d) : Formula 1 d := .conj (.neg (.mem a N))
  (.neg (.existsE (Formula.orderedPairMem 𝒞 a.weaken .newest F.weaken)))
derive_free_closed buni_m
theorem buni_sat_l {d} (ρ : Env M d) (N F a : Term d) :
    Formula.satisfies ρ (buni_m (𝒞 := 𝒞) N F a) ↔ Buni_d I (N.eval ρ) (F.eval ρ) (a.eval ρ) := by
  simp only [buni_m, Buni_d, Formula.satisfies_conj_iff, Formula.satisfies_neg_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_exists_iff, Formula.satisfies_orderedPairMem_iff I,
    Definitional.Term.eval_weaken]; rfl

def Bsem_d (T R N F x V : M.Domain) : Prop := ∃ L U,
  (∀ a, M.mem a L ↔ M.mem a T ∧ Blit_d I F x a) ∧
  (∀ a, M.mem a U ↔ M.mem a T ∧ Buni_d I N F a) ∧ Br_eval_d T R L N U V
def bsem_m {d} (T R N F x V : Term d) : Formula 1 d := .existsE (.existsE (.conj
  (.forallE (.iff (.mem .newest (.bound 2)) (.conj (.mem .newest T.weaken.weaken.weaken)
    (blit_m (𝒞 := 𝒞) F.weaken.weaken.weaken x.weaken.weaken.weaken .newest)))) (.conj
  (.forallE (.iff (.mem .newest (.bound 1)) (.conj (.mem .newest T.weaken.weaken.weaken)
    (buni_m (𝒞 := 𝒞) N.weaken.weaken.weaken F.weaken.weaken.weaken .newest))))
  (br_eval_m T.weaken.weaken R.weaken.weaken (.bound 1) N.weaken.weaken .newest V.weaken.weaken))))
derive_free_closed bsem_m
theorem bsem_sat_l (hE : Extensional M) {d} (ρ : Env M d) (T R N F x V : Term d) :
    Formula.satisfies ρ (bsem_m (𝒞 := 𝒞) T R N F x V) ↔
      Bsem_d I (T.eval ρ) (R.eval ρ) (N.eval ρ) (F.eval ρ) (x.eval ρ) (V.eval ρ) := by
  simp only [bsem_m, Bsem_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_forall_iff, Formula.satisfies_iff_iff, Formula.satisfies_mem_iff,
    blit_sat_l I, buni_sat_l I, br_eval_sat_l hE, Definitional.Term.eval_weaken]; rfl

theorem bsem_exists_unique_l (hZF : M.Models ZF) {T R : M.Domain} (hw : Wf_rel_d T R) (N F x : M.Domain) :
    ∃ V, Bsem_d I T R N F x V ∧ ∀ W, Bsem_d I T R N F x W → W = V := by
  let ρ : Env M 2 := (⟨fun _ => F, fun _ => F⟩ : Env M 1).push x
  let φ : UnarySchema 2 := { body := blit_m (𝒞 := 𝒞) (.bound 2) (.bound 1) .newest }
  let η : Env M 2 := (⟨fun _ => F, fun _ => F⟩ : Env M 1).push N
  let ψ : UnarySchema 2 := { body := buni_m (𝒞 := 𝒞) (.bound 1) (.bound 2) .newest }
  obtain ⟨L, hL'⟩ := ZF.separation_exists_d hZF φ ρ T
  obtain ⟨U, hU'⟩ := ZF.separation_exists_d hZF ψ η T
  have hL a : M.mem a L ↔ M.mem a T ∧ Blit_d I F x a :=
    (hL' a).trans (and_congr_right fun _ => blit_sat_l I _ _ _ _)
  have hU a : M.mem a U ↔ M.mem a T ∧ Buni_d I N F a :=
    (hU' a).trans (and_congr_right fun _ => buni_sat_l I _ _ _ _)
  obtain ⟨V, hv, hu⟩ := br_eval_exists_unique_l hZF hw L N U
  refine ⟨V, ⟨L, U, hL, hU, hv⟩, fun W ⟨L', U', hl', hu', hw'⟩ => ?_⟩
  have e := hZF.1.eq_of_same_members L' L (fun a => (hl' a).trans (hL a).symm)
  subst L'
  have e := hZF.1.eq_of_same_members U' U (fun a => (hu' a).trans (hU a).symm)
  subst U'
  exact hu W hw'

def Bvalue_d (T R N F x : M.Domain) : Prop := ∃ V e,
  Bsem_d I T R N F x V ∧ (∀ a, ¬ M.mem a e) ∧ M.mem e V
def bvalue_m {d} (T R N F x : Term d) : Formula 1 d := .existsE (.existsE (.conj
  (bsem_m (𝒞 := 𝒞) T.weaken.weaken R.weaken.weaken N.weaken.weaken F.weaken.weaken x.weaken.weaken (.bound 1))
  (.conj (Formula.isEmpty .newest) (.mem .newest (.bound 1)))))
derive_free_closed bvalue_m
theorem bvalue_sat_l (hE : Extensional M) {d} (ρ : Env M d) (T R N F x : Term d) :
    Formula.satisfies ρ (bvalue_m (𝒞 := 𝒞) T R N F x) ↔
      Bvalue_d I (T.eval ρ) (R.eval ρ) (N.eval ρ) (F.eval ρ) (x.eval ρ) := by
  simp only [bvalue_m, Bvalue_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    bsem_sat_l I hE, Formula.satisfies_isEmpty_iff, Formula.satisfies_mem_iff, Definitional.Term.eval_weaken]; rfl

def Bsat_d (ω A S c x : M.Domain) : Prop := ∃ T R N F,
  Bpack_d I c T R N F ∧ Btree_d I ω A S T R N F ∧ Bvalue_d I T R N F x
def bsat_m {d} (ω A S c x : Term d) : Formula 1 d := .existsE (.existsE (.existsE (.existsE (.conj
  (bpack_m (𝒞 := 𝒞) c.weaken.weaken.weaken.weaken (.bound 3) (.bound 2) (.bound 1) .newest) (.conj
  (btree_m (𝒞 := 𝒞) ω.weaken.weaken.weaken.weaken A.weaken.weaken.weaken.weaken
    S.weaken.weaken.weaken.weaken (.bound 3) (.bound 2) (.bound 1) .newest)
  (bvalue_m (𝒞 := 𝒞) (.bound 3) (.bound 2) (.bound 1) .newest x.weaken.weaken.weaken.weaken))))))
derive_free_closed bsat_m

theorem bsat_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω A S c x : Term d) :
    Formula.satisfies ρ (bsat_m (𝒞 := 𝒞) ω A S c x) ↔
      Bsat_d I (ω.eval ρ) (A.eval ρ) (S.eval ρ) (c.eval ρ) (x.eval ρ) := by
  simp only [bsat_m, Bsat_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    bpack_sat_l I, btree_sat_l I hE, bvalue_sat_l I hE, Definitional.Term.eval_weaken]; rfl

/-- 已求出的整树真值精确决定该单一码在当前点的根真值。 -/
theorem bsat_root_l (hZF : M.Models ZF) {ω A S c T R N F x V e}
    (hp : Bpack_d I c T R N F) (hc : Btree_d I ω A S T R N F)
    (hv : Bsem_d I T R N F x V) (he : ∀ a, ¬ M.mem a e) : Bsat_d I ω A S c x ↔ M.mem e V := by
  obtain ⟨Z, hz, hu⟩ := bsem_exists_unique_l I hZF hc.wf N F x
  have ev := hu V hv
  constructor
  · rintro ⟨T', R', N', F', hp', _, W, e', hw, he', hm⟩
    obtain ⟨rfl, rfl, rfl, rfl⟩ := bpack_unique_l I hp hp'
    have ew := (hu W hw).trans ev.symm
    have ee := hZF.1.eq_of_same_members e' e (fun a => iff_of_false (he' a) (he a))
    exact ew ▸ ee ▸ hm
  · exact fun h => ⟨T, R, N, F, hp, hc, V, e, hv, he, h⟩

def Bden_d (ω A S B c K : M.Domain) : Prop :=
  ∀ x, M.mem x K ↔ M.mem x B ∧ Bsat_d I ω A S c x
def bden_m {d} (ω A S B c K : Term d) : Formula 1 d := .forallE (.iff (.mem .newest K.weaken)
  (.conj (.mem .newest B.weaken) (bsat_m (𝒞 := 𝒞) ω.weaken A.weaken S.weaken c.weaken .newest)))
derive_free_closed bden_m
theorem bden_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω A S B c K : Term d) :
    Formula.satisfies ρ (bden_m (𝒞 := 𝒞) ω A S B c K) ↔
      Bden_d I (ω.eval ρ) (A.eval ρ) (S.eval ρ) (B.eval ρ) (c.eval ρ) (K.eval ρ) := by
  simp only [bden_m, Bden_d, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_conj_iff, bsat_sat_l I hE, Definitional.Term.eval_weaken]; rfl

/-- 从码和空间直接分离其解释集合，输出唯一。 -/
theorem bden_exists_unique_l (hZF : M.Models ZF) (ω A S B c : M.Domain) :
    ∃ K, Bden_d I ω A S B c K ∧ ∀ L, Bden_d I ω A S B c L → L = K := by
  let ρ : Env M 4 := (((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push A).push S).push c
  let φ : UnarySchema 4 := { body := bsat_m (𝒞 := 𝒞) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  obtain ⟨K, hK'⟩ := ZF.separation_exists_d hZF φ ρ B
  have hK : Bden_d I ω A S B c K := fun x => (hK' x).trans (and_congr_right fun _ => bsat_sat_l I hZF.1 _ _ _ _ _ _)
  exact ⟨K, hK, fun L hL => hZF.1.eq_of_same_members L K (fun x => (hL x).trans (hK x).symm)⟩

end YesMetaZFC.SetTheory.Descriptive
