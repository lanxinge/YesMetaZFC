import YesMetaZFC.SetTheory.InnerModel.OD.RelativeClosure
import YesMetaZFC.Model.SetTheory.ProjectBounded
import YesMetaZFC.SetTheory.KP.Ordinal

/-! # HOD[A] 与 HOD(A) 的实际传递类

两者都以全部成员属于相应参数可定义类的传递容器为见证。遗传闭性和秩切片
由分离构造，后者将提供全收集所需的内部见证集合。
-/
namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

def Ha_d (k : Bool) (A x : M.Domain) : Prop :=
  ∃ T, M.TransitiveSet T ∧ M.mem x T ∧ ∀ y, M.mem y T → Oa_d k A y
abbrev Hb_d (A x : M.Domain) := Ha_d false A x
abbrev Hp_d (A x : M.Domain) := Ha_d true A x

def ha_m {d} (k : Bool) (A x : Term d) : Formula 1 d := .existsE
  (.conj (Formula.isTransitive .newest) (.conj (.mem x.weaken .newest)
    (Formula.forallMem .newest (oa_m k A.weaken.weaken .newest))))
@[simp] theorem ha_closed_l {d} (k : Bool) (A x : Term d) (hA : A.freeSupport = []) (hx : x.freeSupport = []) :
    (ha_m k A x).FreeClosed := by simp -implicitDefEqProofs [ha_m, Definitional.Formula.FreeClosed, hA, hx]

theorem ha_sat_l (hE : Extensional M) {d} (ρ : Env M d) (k : Bool) (A x : Term d) :
    Formula.satisfies ρ (ha_m k A x) ↔ Ha_d k (A.eval ρ) (x.eval ρ) := by
  simp only [ha_m, Ha_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_isTransitive_iff, Formula.satisfies_mem_iff, Formula.satisfies_forallMem_iff,
    oa_sat_l hE, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]

theorem ha_oa_l {k A x} (h : Ha_d (M := M) k A x) : Oa_d k A x := h.elim fun _ h => h.2.2 x h.2.1
theorem ha_trans_l {k A x y} (h : Ha_d (M := M) k A x) (hy : M.mem y x) : Ha_d k A y := by
  obtain ⟨T, ht, hx, ho⟩ := h
  exact ⟨T, ht, ht x hx y hy, ho⟩

theorem ha_ordinal_l (hZF : M.Models ZF) (k : Bool) (A : M.Domain) {x} (hx : M.IsOrdinal x) : Ha_d k A x := by
  obtain ⟨s, hs, hxs⟩ := KP.ordinal_successor_l (ZF.modelsKP hZF) hx
  exact ⟨s, hs.transitive, hxs.predecessor_mem, fun y hy => oa_ordinal_l hZF k A (hs.mem hy)⟩

/-- 可定义集合的成员已遗传可定义时，分离出一个遗传容器即可。 -/
theorem ha_of_members_l (hZF : M.Models ZF) {k A x} (hx : Oa_d (M := M) k A x)
    (hm : ∀ y, M.mem y x → Ha_d k A y) : Ha_d k A x := by
  obtain ⟨a, V, hv, hxm⟩ := ZF.v_cover_l (kp_pair_l (ZF.modelsKP hZF)) hZF x
  have ht := ZF.v_transitive_l (kp_pair_l (ZF.modelsKP hZF)) hZF hv
  let ρ : Env M 2 := ⟨Fin.cases x (fun _ => A), fun _ => x⟩
  let φ : UnarySchema 2 := { body := .disj (Formula.extensionalEq .newest (.bound 1)) (ha_m k (.bound 2) .newest) }
  have sat y : φ.denote ρ y ↔ y = x ∨ Ha_d k A y := by
    simp only [UnarySchema.denote, φ, Formula.satisfies_disj_iff,
      Formula.satisfies_extensionalEq_iff_eq hZF.1, ha_sat_l hZF.1]
    rfl
  obtain ⟨T, hT'⟩ := ZF.separation_exists_d hZF φ ρ V
  have hT y : M.mem y T ↔ M.mem y V ∧ (y = x ∨ Ha_d k A y) := (hT' y).trans (and_congr_right fun _ => sat y)
  refine ⟨T, ?_, (hT x).mpr ⟨hxm, Or.inl rfl⟩, fun y hy =>
    ((hT y).mp hy).2.elim (fun he => he.symm ▸ hx) ha_oa_l⟩
  intro y hy z hz
  obtain ⟨hyV, hy⟩ := (hT y).mp hy
  exact (hT z).mpr ⟨ht y hyV z hz, Or.inr (hy.elim (fun he => hm z (he ▸ hz)) (fun h => ha_trans_l h hz))⟩

def ha_cut_s (k : Bool) : UnarySchema 2 := {
  body := .existsE (.conj (v_m kpair_convention_l (.bound 2) .newest) (.forallE (.iff (.mem .newest (.bound 2))
    (.conj (.mem .newest (.bound 1)) (ha_m k (.bound 4) .newest))))) }

theorem ha_cut_l (hZF : M.Models ZF) (k : Bool) (A : M.Domain) {a V}
    (hV : V_d (kp_pair_l (ZF.modelsKP hZF)) a V) :
    ∃ S, Ha_d k A S ∧ ∀ y, M.mem y S ↔ M.mem y V ∧ Ha_d k A y := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  let φ : UnarySchema 1 := { body := ha_m k (.bound 1) .newest }
  obtain ⟨S, hS'⟩ := ZF.separation_exists_d hZF φ ⟨fun _ => A, fun _ => A⟩ V
  have hS y : M.mem y S ↔ M.mem y V ∧ Ha_d k A y :=
    (hS' y).trans (and_congr_right fun _ => ha_sat_l hZF.1 _ _ _ _)
  let ρ : Env M 2 := ⟨Fin.cases a (fun _ => A), fun _ => A⟩
  have sat Y : (ha_cut_s k).denote ρ Y ↔ ∃ W, V_d I a W ∧ ∀ y, M.mem y Y ↔ M.mem y W ∧ Ha_d k A y := by
    simp only [ha_cut_s, UnarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      v_sat_l I hZF.1, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff, Formula.satisfies_mem_iff, ha_sat_l hZF.1]
    rfl
  have hs : Oa_d k A S := by
    apply oa_unique_l hZF k A (ha_cut_s k) ρ
      (Fin.cases (oa_ordinal_l hZF k A (v_ordinal_l I hV)) (fun _ => oa_parameter_l hZF k A))
    intro Y
    refine (sat Y).trans ⟨?_, fun he => he.symm ▸ ⟨V, hV, hS⟩⟩
    rintro ⟨W, hw, hy⟩
    have eq := ZF.v_unique_l I hZF hw hV; subst W
    exact hZF.1.eq_of_same_members Y S (fun y => (hy y).trans (hS y).symm)
  exact ⟨S, ha_of_members_l hZF hs (fun y hy => ((hS y).mp hy).2), hS⟩

def ha_model_l (hZF : M.Models ZF) (k : Bool) (A : M.Domain) : Structure.{u} where
  Domain := {x : M.Domain // Ha_d k A x}
  nonempty := by
    obtain ⟨e, he⟩ := KP.exists_empty (ZF.modelsKP hZF)
    exact ⟨⟨e, ha_ordinal_l hZF k A (Structure.IsOrdinal.of_no_members he)⟩⟩
  mem x y := M.mem x.val y.val

theorem ha_model_ext_l (hZF : M.Models ZF) (k : Bool) (A : M.Domain) : Extensional (ha_model_l hZF k A) := by
  refine ⟨fun x y h => Subtype.ext (hZF.1.eq_of_same_members x.val y.val (fun z => ?_))⟩
  exact ⟨fun hz => (h ⟨z, ha_trans_l x.property hz⟩).mp hz, fun hz => (h ⟨z, ha_trans_l y.property hz⟩).mpr hz⟩

theorem ha_model_delta_l (hZF : M.Models ZF) (k : Bool) (A : M.Domain) {n}
    {φ : Formula 1 n} (hφ : φ.IsDelta0) (ρ : Env (ha_model_l hZF k A) n) :
    Formula.satisfies ρ φ ↔ Formula.satisfies (image_env_l Subtype.val ρ) φ :=
  delta0_image_l (M := ha_model_l hZF k A) (N := M) Subtype.val (fun _ _ h => Subtype.ext h)
    (fun x y => ⟨fun h => ⟨⟨y, ha_trans_l x.property h⟩, h, rfl⟩, fun ⟨_, h, he⟩ => he ▸ h⟩) hφ ρ

end YesMetaZFC.SetTheory.InnerModel
