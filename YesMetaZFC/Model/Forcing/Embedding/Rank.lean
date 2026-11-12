import YesMetaZFC.Model.SetTheory.ProjectEmbedding
import YesMetaZFC.Model.SetTheory.ProjectBounded
import YesMetaZFC.Model.Forcing.Extension.Choice
import YesMetaZFC.Model.Forcing.TwoStep.Basic
import YesMetaZFC.Model.Forcing.Ground.Collapse
import YesMetaZFC.Model.Forcing.Order.GlobalDense
import YesMetaZFC.Model.SetTheory.Embedding.PredicateTrace
import YesMetaZFC.Model.SetTheory.Embedding.RankFixed
import YesMetaZFC.SetTheory.CumulativeRelativeClosure
import YesMetaZFC.Model.SetTheory.Internal.RealTrace

/-! # 初等嵌入保持内部名称与原力迫关系

名称、规范名称及力迫关系均使用已构造的原一阶公式。这里搬运同一公式，
不另设名称递归或力迫真值的操作参数。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
open SetTheory.Definitional.Project.FirstOrderSemantics
universe u v
variable {M : Structure.{u}} {N : Structure.{v}}
variable (hM : Extensional M) (hN : Extensional N)
  (j : M.Domain → N.Domain) (hj : Pe_d j)
local notation "e" => j
include hM hN hj

theorem em_name_l {P t : M.Domain} : Name_d M P t ↔ Name_d N (e P) (e t) := by
  let ρ : Env M 2 := ⟨Fin.cases t (fun _ => P), fun _ => P⟩
  exact (name_sat_l M hM ρ (.bound 1) .newest).symm.trans
    ((hj (name_m (.bound 1) .newest) (by simp -implicitDefEqProofs) ρ).trans
      (name_sat_l N hN (image_env_l e ρ) (.bound 1) .newest))

theorem em_check_l {p a t : M.Domain} : Check_d M p a t ↔ Check_d N (e p) (e a) (e t) := by
  let ρ : Env M 3 := ⟨Fin.cases t (Fin.cases a (fun _ => p)), fun _ => p⟩
  exact (check_sat_l M hM ρ (.bound 2) (.bound 1) .newest).symm.trans
    ((hj (check_m (.bound 2) (.bound 1) .newest)
      (by simp -implicitDefEqProofs) ρ).trans (check_sat_l N hN (image_env_l e ρ) (.bound 2) (.bound 1) .newest))

theorem em_eq_force_l {P R z p s t : M.Domain} :
    Eq_force_d M P R z p s t ↔ Eq_force_d N (e P) (e R) (e z) (e p) (e s) (e t) := by
  let ρ : Env M 6 := ⟨fun i => [t,s,p,z,R,P].get i, fun _ => P⟩
  exact (eq_force_sat_l M hM ρ (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest).symm.trans
    ((hj (eq_force_m (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest)
      (by simp -implicitDefEqProofs) ρ).trans
      (eq_force_sat_l N hN (image_env_l e ρ) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest))

omit hM hN in
theorem em_forces_l {n} (φ : Formula 1 n) (hc : φ.FreeClosed) (ρ : Env M n) (P R z p : M.Domain) :
    Forces_d M P R z φ ρ p ↔ Forces_d N (e P) (e R) (e z) φ (image_env_l e ρ) (e p) := by
  have tr := hj (force_code_m φ) (force_code_closed_l φ hc) (fenv_l ρ P R z p)
  have env : @image_env_l M N e (n + 4) (fenv_l ρ P R z p) =
      fenv_l (image_env_l e ρ) (e P) (e R) (e z) (e p) := by
    exact congrArg (fun b => (⟨b, fun i => e (ρ.free i)⟩ : Env N (n + 4)))
      (funext (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl))))))
  exact tr.trans (iff_of_eq (congrArg (fun η : Env N (n + 4) => Formula.satisfies η (force_code_m φ)) env))

theorem em_order_l {P R z : M.Domain} (O : Cond_order_d M P R z) : Cond_order_d N (e P) (e R) (e z) := by
  let ρ : Env M 3 := ⟨Fin.cases z (Fin.cases R (fun _ => P)), fun _ => P⟩
  exact (cond_order_sat_l hN (image_env_l e ρ) (.bound 2) (.bound 1) .newest).mp
    ((hj (cond_order_m (.bound 2) (.bound 1) .newest)
      (by simp -implicitDefEqProofs) ρ).mp ((cond_order_sat_l hM ρ (.bound 2) (.bound 1) .newest).mpr O))

end YesMetaZFC.Model.Forcing.Internal

/-! ## 初等嵌入的实际泛型商提升

按 [τ]↦[j(τ)] 直接定义商映射。接受原泛型条件的像保证代表元无关；
完整初等性由原力迫真值定理和否定反射给出。构造不选取商代表元。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
open SetTheory.Definitional.Project.FirstOrderSemantics
universe u v
variable {M : Structure.{u}} {N : Structure.{v}}
variable {P R z : M.Domain} {U : M.Domain → Prop} {V : N.Domain → Prop}
section Quotient
variable (hM : Extensional M) (hN : Extensional N)
  (j : M.Domain → N.Domain) (hj : Pe_d j) (accepted : ∀ p, U p → V (j p))
local notation "e" => j
include hM hN hj accepted

def em_lift_l : Name_quot_l M P R z U → Name_quot_l N (e P) (e R) (e z) V :=
  Quot.lift (fun t : {t : M.Domain // Name_d M P t} =>
    Quot.mk (Name_eq_d N (e P) (e R) (e z) V) ⟨e t.1, (em_name_l hM hN j hj).mp t.2⟩) (by
    rintro s t ⟨p, hp, eq⟩
    exact Quot.sound ⟨e p, accepted p hp, (em_eq_force_l hM hN j hj).mp eq⟩)

theorem em_lift_value_l {t x} (value : Qval_d M P R z U t x) :
    Qval_d N (e P) (e R) (e z) V (e t) (em_lift_l hM hN j hj accepted x) := by
  obtain ⟨ht, rfl⟩ := value
  exact ⟨(em_name_l hM hN j hj).mp ht, rfl⟩

end Quotient

variable (hM : M.Models ZF) (hN : N.Models ZF)
  (j : M.Domain → N.Domain) (hj : Pe_d j) (accepted : ∀ p, U p → V (j p))
local notation "e" => j
include hM hN hj accepted
variable (O : Cond_order_d M P R z) (hU : Generic_d M P R z U)
  (hV : Generic_d N (j P) (j R) (j z) V)
local notation "E" => extension_l M hM P R z U
local notation "D" => extension_l N hN (e P) (e R) (e z) V
include O hU hV

theorem em_lift_elementary_l {n} (φ : Formula 1 n) (hc : φ.FreeClosed) (ρ : Env E n) :
    Formula.satisfies ρ φ ↔ Formula.satisfies
      (@image_env_l E D (em_lift_l hM.1 hN.1 j hj accepted (P := P) (R := R) (z := z)) n ρ) φ := by
  let f : (E).Domain → (D).Domain := em_lift_l hM.1 hN.1 j hj accepted
  have target := em_order_l hM.1 hN.1 j hj O
  obtain ⟨η, values⟩ := lift_env_l hM ρ
  have values' : Env_val_d hN (@image_env_l M N e n η) (@image_env_l E D f n ρ) := by
    intro t
    cases t with
    | bound i => exact em_lift_value_l hM.1 hN.1 j hj accepted (values (.bound i))
    | free i => exact em_lift_value_l hM.1 hN.1 j hj accepted (values (.free i))
  have forward (ψ : Formula 1 n) (hs : ψ.FreeClosed) (h : Formula.satisfies ρ ψ) :
      Formula.satisfies (image_env_l f ρ) ψ := by
    obtain ⟨p, hp, forced⟩ := (forcing_truth_l O hM hU ψ hs η ρ values).mpr h
    exact (forcing_truth_l target hN hV ψ hs (image_env_l e η) (image_env_l f ρ) values').mp
      ⟨e p, accepted p hp, (em_forces_l j hj ψ hs η P R z p).mp forced⟩
  refine ⟨forward φ hc, fun h => Classical.byContradiction (fun no => ?_)⟩
  exact forward (.neg φ) hc no h

theorem em_lift_injective_l : Function.Injective (em_lift_l hM.1 hN.1 j hj accepted (P := P) (R := R) (z := z)) := by
  intro x y eq
  let ρ : Env E 2 := ⟨Fin.cases y (fun _ => x), fun _ => x⟩
  have tr := em_lift_elementary_l hM hN j hj accepted O hU hV
    (Formula.extensionalEq (.bound 1) .newest) (by simp -implicitDefEqProofs) ρ
  exact (Formula.satisfies_extensionalEq_iff_eq (extension_ext_l O hM hU) ρ (.bound 1) .newest).mp
    (tr.mpr ((Formula.satisfies_extensionalEq_iff_eq (extension_ext_l (em_order_l hM.1 hN.1 j hj O) hN hV)
      (@image_env_l E D (em_lift_l hM.1 hN.1 j hj accepted (P := P) (R := R) (z := z)) 2 ρ)
        (.bound 1) .newest).mpr eq))

/-- 自动构造两侧规范地嵌入，并验证提升与原嵌入的交换方块。 -/
theorem em_lift_ground_l {p : M.Domain} (hp : U p) :
    ∃ a : M.Domain → (E).Domain, ∃ b : N.Domain → (D).Domain,
      (∀ x t, Check_d M p x t → Qval_d M P R z U t (a x)) ∧
      (∀ y t, Check_d N (e p) y t → Qval_d N (e P) (e R) (e z) V t (b y)) ∧
      ∀ x, em_lift_l hM.1 hN.1 j hj accepted (a x) = b (e x) := by
  obtain ⟨a, ha, _, _⟩ := check_map_l O hM hU hp
  obtain ⟨b, hb, _, _⟩ := check_map_l (em_order_l hM.1 hN.1 j hj O) hN hV (accepted p hp)
  refine ⟨a, b, ha, hb, fun x => ?_⟩
  obtain ⟨t, ht, _⟩ := zf_check_l M hM (hU.proper p hp).1 x
  exact qval_unique_l (em_lift_value_l hM.1 hN.1 j hj accepted (ha x t ht))
    (hb (e x) (e t) ((em_check_l hM.1 hN.1 j hj).mp ht))

end YesMetaZFC.Model.Forcing.Internal

/-! ## 旧小偏序的泛型性向初等目标传递

把目标稠密集先与条件域相交，再取其实际旧原像。所有目标条件都有旧来源，
所以稠密性反射回源模型，源泛型性即可遇到目标稠密集。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
open SetTheory.Definitional.Project.FirstOrderSemantics
universe u v
variable {M : Structure.{u}} {N : Structure.{v}}
section Relations
variable (hM : Extensional M) (hN : Extensional N)
  (j : M.Domain → N.Domain) (hj : Pe_d j)
local notation "e" => j
include hM hN hj

omit hM hN in
theorem em_member_l (a b : M.Domain) : M.mem a b ↔ N.mem (e a) (e b) := by
  let ρ : Env M 2 := ⟨Fin.cases b (fun _ => a), fun _ => a⟩
  let φ : Formula 1 2 := .mem (.bound 1) .newest
  have hc : φ.FreeClosed := by simp -implicitDefEqProofs [φ, Definitional.Formula.FreeClosed]
  exact hj φ hc ρ

theorem em_entry_l (a b R : M.Domain) : Entry_d M a b R ↔ Entry_d N (e a) (e b) (e R) := by
  let ρ : Env M 3 := ⟨Fin.cases R (Fin.cases b (fun _ => a)), fun _ => a⟩
  exact (entry_sat_l M hM ρ (.bound 2) (.bound 1) .newest).symm.trans
    ((hj (entry_m (.bound 2) (.bound 1) .newest)
      (by simp -implicitDefEqProofs) ρ).trans (entry_sat_l N hN (image_env_l e ρ) (.bound 2) (.bound 1) .newest))

theorem em_below_l (P R z q p : M.Domain) :
    Below_d M P R z q p ↔ Below_d N (e P) (e R) (e z) (e q) (e p) :=
  and_congr (em_member_l j hj q P) (and_congr
    (not_congr ⟨congrArg e, fun h => hj.injective_l hM hN h⟩) (em_entry_l hM hN j hj q p R))

end Relations

def Em_generic_d {M : Structure.{u}} {N : Structure.{v}}
    (f : M.Domain → N.Domain) (U : M.Domain → Prop) (q : N.Domain) : Prop :=
  ∃ p, U p ∧ f p = q

section Generic
variable (hM : Extensional M) (hN : N.Models KP) (j : M.Domain → N.Domain) (hj : Pe_d j)
local notation "e" => j
include hM hN hj

theorem em_generic_l {P R z : M.Domain} {U : M.Domain → Prop}
    (hU : Generic_d M P R z U)
    (conditions : ∀ q, N.mem q (e P) → ∃ p, M.mem p P ∧ e p = q)
    (subsets : ∀ D, N.MemberSubset D (e P) → ∃ C, e C = D) :
    Generic_d N (e P) (e R) (e z) (Em_generic_d e U) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rintro q ⟨p, hp, rfl⟩
    exact ⟨(em_member_l j hj p P).mp (hU.proper p hp).1,
      fun eq => (hU.proper p hp).2 (hj.injective_l hM hN.1 eq)⟩
  · obtain ⟨p, hp⟩ := hU.inhabited
    exact ⟨e p, p, hp, rfl⟩
  · rintro p q ⟨a, ha, rfl⟩ hq pq
    obtain ⟨b, hb, rfl⟩ := conditions q hq
    exact ⟨b, hU.upward a b ha hb ((em_entry_l hM hN.1 j hj a b R).mpr pq), rfl⟩
  · rintro p q ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    obtain ⟨c, hc, ca, cb⟩ := hU.directed a b ha hb
    exact ⟨e c, ⟨c, hc, rfl⟩, (em_entry_l hM hN.1 j hj c a R).mp ca, (em_entry_l hM hN.1 j hj c b R).mp cb⟩
  · rintro p ⟨a, ha, rfl⟩ D dense
    obtain ⟨K, inter⟩ := KP.intersection_exists_d hN D (e P)
    obtain ⟨C, eq⟩ := subsets K (fun q hq => ((inter q).mp hq).2)
    have dense' : Dense_d M P R z (fun q => M.mem q C) a := by
      intro b hb
      obtain ⟨q, hq, hd⟩ := dense (e b) ((em_below_l hM hN.1 j hj P R z b a).mp hb)
      obtain ⟨c, _, rfl⟩ := conditions q hq.1
      exact ⟨c, (em_below_l hM hN.1 j hj P R z c b).mpr hq,
        (em_member_l j hj c C).mpr (eq.symm ▸ (inter (e c)).mpr ⟨hd, hq.1⟩)⟩
    obtain ⟨q, hq, qc⟩ := hU.meets a ha C dense'
    exact ⟨e q, ⟨q, hq, rfl⟩, ((inter (e q)).mp (eq ▸ (em_member_l j hj q C).mp qc)).1⟩

end Generic

variable (hM : M.Models ZF) (hN : N.Models ZF) (j : M.Domain → N.Domain) (hj : Pe_d j)
local notation "e" => j
include hj

/-- 完整条件像及子集像已经足够，目标泛型性在此实际证明。 -/
theorem em_small_lift_l {P R z : M.Domain} {U : M.Domain → Prop}
    (O : Cond_order_d M P R z) (hU : Generic_d M P R z U)
    (conditions : ∀ q, N.mem q (e P) → ∃ p, M.mem p P ∧ e p = q)
    (subsets : ∀ D, N.MemberSubset D (e P) → ∃ C, e C = D) :
    let V := Em_generic_d e U
    Generic_d N (e P) (e R) (e z) V ∧
    ∃ f : (extension_l M hM P R z U).Domain → (extension_l N hN (e P) (e R) (e z) V).Domain,
      Function.Injective f ∧
      (∀ t x, Qval_d M P R z U t x → Qval_d N (e P) (e R) (e z) V (e t) (f x)) ∧
      ∀ {n} (φ : Formula 1 n), φ.FreeClosed → ∀ ρ, Formula.satisfies ρ φ ↔ Formula.satisfies (image_env_l f ρ) φ := by
  have hV := em_generic_l hM.1 (ZF.modelsKP hN) j hj hU conditions subsets
  have accepted p (hp : U p) : Em_generic_d e U (e p) := ⟨p, hp, rfl⟩
  exact ⟨hV, em_lift_l hM.1 hN.1 j hj accepted, em_lift_injective_l hM hN j hj accepted O hU hV,
    fun _ _ => em_lift_value_l hM.1 hN.1 j hj accepted, em_lift_elementary_l hM hN j hj accepted O hU hV⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 成员同构沿同一泛型扩张提升

目标稠密集由同构满射实际回拉。名字商上的提升仍为满射，因为每个目标名字
都有原名字；规范地值的交换方程保留原模型的每个参数。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u v k
variable {M : Structure.{u}} {N : Structure.{v}} (hM : M.Models ZF) (hN : N.Models ZF)

theorem iso_extension_l (e : M.Domain → N.Domain)
    (onto : Function.Surjective e) (mem : ∀ x y, M.mem x y ↔ N.mem (e x) (e y))
    {B R z : M.Domain} (O : Cond_order_d M B R z) {G : M.Domain → Prop}
    (generic : Generic_d M B R z G) :
    Generic_d N (e B) (e R) (e z) (Em_generic_d e G) ∧
      Miso_over_d (extension_l M hM B R z G) (extension_l N hN (e B) (e R) (e z) (Em_generic_d e G))
        (Gval_d M B R z G) (fun x => Gval_d N (e B) (e R) (e z) (Em_generic_d e G) (e x)) := by
  have elem : Pe_d e := fun φ _ ρ => formula_image_l e onto mem φ ρ
  have target := em_order_l hM.1 hN.1 e elem O
  have moved : Generic_d N (e B) (e R) (e z) (Em_generic_d e G) :=
    em_generic_l hM.1 (ZF.modelsKP hN) e elem generic
      (fun q hq => by
        obtain ⟨p,rfl⟩ := onto q
        exact ⟨p,(mem p B).mpr hq,rfl⟩) (fun D _ => onto D)
  have accepted p (hp : G p) : Em_generic_d e G (e p) := ⟨p,hp,rfl⟩
  let f := em_lift_l hM.1 hN.1 e elem accepted (P := B) (R := R) (z := z)
  have fi := em_lift_injective_l hM hN e elem accepted O generic moved
  have fm x y : (extension_l M hM B R z G).mem x y ↔
      (extension_l N hN (e B) (e R) (e z) (Em_generic_d e G)).mem (f x) (f y) := by
    let ρ : Env (extension_l M hM B R z G) 2 := ⟨Fin.cases y (fun _ => x),fun _ => x⟩
    exact em_lift_elementary_l hM hN e elem accepted O generic moved
      (.mem (.bound 1) .newest) (by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed]) ρ
  have fs : Function.Surjective f := by
    intro y
    obtain ⟨t,nt,ty⟩ := value_name_l y
    obtain ⟨s,rfl⟩ := onto t
    have ns := (em_name_l hM.1 hN.1 e elem).mpr nt
    obtain ⟨x,sx⟩ := name_value_l (R := R) (z := z) (U := G) ns
    exact ⟨x,qval_unique_l (em_lift_value_l hM.1 hN.1 e elem accepted sx) ty⟩
  have forward x y (hy : Gval_d M B R z G x y) :
      Gval_d N (e B) (e R) (e z) (Em_generic_d e G) (e x) (f y) := by
    obtain ⟨p,t,hp,check,value⟩ := hy
    exact ⟨e p,e t,accepted p hp,(em_check_l hM.1 hN.1 e elem).mp check,
      em_lift_value_l hM.1 hN.1 e elem accepted value⟩
  refine ⟨moved,f,fm,fi,fs,fun x y => ⟨forward x y,fun hy => ?_⟩⟩
  obtain ⟨v,hv⟩ := gval_exists_l hM generic x
  exact fi ((forward x v hv).unique_l target hN moved hy) ▸ hv

/-- 保持同一地参数的中间同构，把同一个外部滤子继续提升到两侧第二步扩张。 -/
theorem Miso_over_d.iterate_l {A : Structure.{k}} {j : A.Domain → M.Domain} {k : A.Domain → N.Domain}
    (iso : Miso_over_d M N (fun x y => j x = y) (fun x y => k x = y))
    {B R z : A.Domain} (O : Cond_order_d M (j B) (j R) (j z)) {G : A.Domain → Prop}
    (generic : Generic_d M (j B) (j R) (j z) (Em_generic_d j G)) :
    Generic_d N (k B) (k R) (k z) (Em_generic_d k G) ∧
      Miso_over_d (extension_l M hM (j B) (j R) (j z) (Em_generic_d j G))
        (extension_l N hN (k B) (k R) (k z) (Em_generic_d k G))
        (fun x => Gval_d M (j B) (j R) (j z) (Em_generic_d j G) (j x))
        (fun x => Gval_d N (k B) (k R) (k z) (Em_generic_d k G) (k x)) := by
  obtain ⟨f,mem,_,onto,over⟩ := iso
  have square x : f (j x) = k x := ((over x (j x)).mp rfl).symm
  have same : Em_generic_d f (Em_generic_d j G) = Em_generic_d k G := by
    funext y
    apply propext
    constructor
    · rintro ⟨v,⟨x,hx,rfl⟩,eq⟩
      exact ⟨x,hx,(square x).symm.trans eq⟩
    · rintro ⟨x,hx,rfl⟩
      exact ⟨j x,⟨x,hx,rfl⟩,square x⟩
  obtain ⟨generic',comparison⟩ := iso_extension_l hM hN f onto mem O generic
  have comparison := comparison.comp_l j
  rw [square B,square R,square z,same] at generic' comparison
  exact ⟨generic',by simpa only [square] using comparison⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 覆盖全局稠密集即可传递实际泛型性

目标局部要求先扩充为全局稠密集，再拉回源模型。命中后由滤子相容性排除
不相容分支；不要求目标全部子集均有原像。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.Definitional.Project.FirstOrderSemantics
universe u v
variable {M : Structure.{u}} {N : Structure.{v}}
variable (hM : Extensional M) (hN : N.Models ZF) (j : M.Domain → N.Domain) (elem : Pe_d j)
include hM hN elem

theorem em_global_generic_l {P R z : M.Domain} {G : M.Domain → Prop}
    (O : Cond_order_d M P R z) (generic : Generic_d M P R z G)
    (conditions : ∀ q, N.mem q (j P) → ∃ p, M.mem p P ∧ j p = q)
    (globals : ∀ D, Dense_set_d N (j P) (j R) (j z) D → ∃ C, j C = D) :
    Generic_d N (j P) (j R) (j z) (Em_generic_d j G) := by
  have order := em_order_l hM hN.1 j elem O
  have member := em_member_l j elem
  have edge := em_entry_l hM hN.1 j elem
  have below := em_below_l hM hN.1 j elem
  refine ⟨?_,?_,?_,?_,?_⟩
  · rintro q ⟨p,hp,rfl⟩
    exact ⟨(member p P).mp (generic.proper p hp).1,fun eq => (generic.proper p hp).2 (elem.injective_l hM hN.1 eq)⟩
  · obtain ⟨p,hp⟩ := generic.inhabited
    exact ⟨j p,p,hp,rfl⟩
  · rintro p q ⟨a,ha,rfl⟩ hq pq
    obtain ⟨b,hb,rfl⟩ := conditions q hq
    exact ⟨b,generic.upward a b ha hb ((edge a b R).mpr pq),rfl⟩
  · rintro p q ⟨a,ha,rfl⟩ ⟨b,hb,rfl⟩
    obtain ⟨r,hr,ra,rb⟩ := generic.directed a b ha hb
    exact ⟨j r,⟨r,hr,rfl⟩,(edge r a R).mp ra,(edge r b R).mp rb⟩
  · rintro p ⟨a,ha,rfl⟩ D dense
    obtain ⟨E,global,read⟩ := dense_globalize_l hN order ((member a P).mp (generic.proper a ha).1) dense
    obtain ⟨C,eq⟩ := globals E global
    have dense' : Dense_d M P R z (fun q => M.mem q C) a := by
      intro p hp
      have jp := (below P R z p a).mp hp
      obtain ⟨q,qp,qE⟩ := global.2 (j p) jp.1 jp.2.1
      obtain ⟨r,_,rfl⟩ := conditions q qp.1
      exact ⟨r,(below P R z r p).mpr qp,(member r C).mpr (eq.symm ▸ qE)⟩
    obtain ⟨q,hq,qC⟩ := generic.meets a ha C dense'
    rcases ((read (j q)).mp (eq ▸ (member q C).mp qC)).2.2 with no | hit
    · obtain ⟨r,hr,rq,ra⟩ := generic.directed q a hq ha
      have rp := generic.proper r hr
      exact (no ⟨j r,(below P R z r q).mp ⟨rp.1,rp.2,rq⟩,(edge r a R).mp ra⟩).elim
    · exact ⟨j q,⟨q,hq,rfl⟩,hit.2⟩

omit hM hN elem in
theorem em_dense_family_l (hM : Extensional M) (hN : Extensional N)
    (elem : Pe_d j) {P R z E : M.Domain}
    (family : ∀ D, M.mem D E ↔ Dense_set_d M P R z D) :
    ∀ D, N.mem D (j E) ↔ Dense_set_d N (j P) (j R) (j z) D := by
  let φ : Formula 1 4 := set[4] ⟪∀ D,
    D ∈ ⌜(.bound 3 : Term 4)⌝ₛ ↔
      ⌜dense_set_m⌝ₚ(⌜(.bound 0 : Term 4)⌝ₛ,⌜(.bound 1 : Term 4)⌝ₛ,⌜(.bound 2 : Term 4)⌝ₛ,D)⟫
  let ρ : Env M 4 := ⟨fun i => [P,R,z,E].get i,fun _ => P⟩
  have transfer := elem φ (by simp -implicitDefEqProofs [φ,Definitional.Formula.FreeClosed,dense_set_m_freeClosed]) ρ
  simp only [φ,Formula.satisfies_forall_iff,Formula.satisfies_iff_iff,Formula.satisfies_mem_iff,
    dense_set_sat_l M hM,dense_set_sat_l N hN,Definitional.Term.eval_weaken] at transfer
  exact transfer.mp family

end YesMetaZFC.Model.Forcing.Internal

/-! ## 共同低秩段上的实际小力迫提升

迭代已有的共同相对秩段和临界点以下固定性，自动给出条件及所有目标
稠密集的旧原像。随后实际证明目标泛型性并构造 [τ]↦[j(τ)] 的初等提升。
共同层中的每个名字值还满足成员满性，目标值不会多出源值没有的成员。
这里保留源内幂集，不把它替换为背景幂集。
-/
namespace YesMetaZFC.SetTheory
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

namespace Internal
open YesMetaZFC.Model.Forcing.Internal

theorem Smap_d.rank_lift_l {ω c d X R Y S j κ ℓ V : M.Domain}
    (hw : M.IsOmega ω) (xt : M.TransitiveSet X) (yt : M.TransitiveSet Y)
    (mx : Smem_d I c X R) (my : Smem_d I d Y S) (map : Smap_d I ω c d X Y j)
    (hκ : Rd_entry_d κ ℓ j) (fixed : ∀ β, M.mem β κ → Rd_entry_d β β j)
    (hVX : M.mem V X) (rx : Vr_d X κ V) (hVY : M.mem V Y) (ry : Vr_d Y κ V)
    (hA : (smdl_structure_l I (R := R) mx.1.2.1).Models ZF)
    (hB : (smdl_structure_l I (R := S) my.1.2.1).Models ZF)
    (P Q z : (smdl_structure_l I (R := R) mx.1.2.1).Domain) (hp : M.mem P.val V)
    (O : Cond_order_d _ P Q z) {U} (generic : Generic_d _ P Q z U) :
    ∃ e : (smdl_structure_l I (R := R) mx.1.2.1).Domain → (smdl_structure_l I (R := S) my.1.2.1).Domain,
      Pe_d e ∧ (∀ x, Rd_entry_d x.val (e x).val j) ∧
      Generic_d _ (e P) (e Q) (e z) (Em_generic_d e U) ∧
      (∀ q, Em_generic_d e U q ↔ ∃ p, U p ∧ p.val = q.val) ∧
      ∃ f : (extension_l _ hA P Q z U).Domain → (extension_l _ hB (e P) (e Q) (e z) (Em_generic_d e U)).Domain,
        Function.Injective f ∧
        (∀ t x, Qval_d _ P Q z U t x → Qval_d _ (e P) (e Q) (e z) (Em_generic_d e U) (e t) (f x)) ∧
        (∀ {n} (φ : Formula 1 n), φ.FreeClosed → ∀ ρ, Formula.satisfies ρ φ ↔ Formula.satisfies (image_env_l f ρ) φ) ∧
        ∀ τ : (smdl_structure_l I (R := R) mx.1.2.1).Domain, M.mem τ.val V →
          ∀ x, Qval_d _ P Q z U τ x → ∀ y,
          (extension_l _ hB (e P) (e Q) (e z) (Em_generic_d e U)).mem y (f x) ↔
            ∃ t, (extension_l _ hA P Q z U).mem t x ∧ f t = y := by
  let A := smdl_structure_l I (R := R) mx.1.2.1
  let B := smdl_structure_l I (R := S) my.1.2.1
  obtain ⟨e, elem, values⟩ := map.project_l I hZF hw mx.1 my.1
  have low := map.rank_fixed_l hZF hw xt yt mx my hκ fixed hVX rx hVY ry
  have vt := rx.transitive_l xt hVX
  have value (a : A.Domain) (ha : M.mem a.val V) : (e a).val = a.val :=
    map.1.1.1.2 a.val (e a).val a.val (values a) (low a.val ha)
  have eP := value P hp
  have conditions (q : B.Domain) (hq : B.mem q (e P)) : ∃ p : A.Domain, A.mem p P ∧ e p = q := by
    have qP : M.mem q.val P.val := eP ▸ ((my.2 q.val (e P).val).mp hq).2.2
    let p : A.Domain := ⟨q.val, xt V hVX q.val (vt P.val hp q.val qP)⟩
    exact ⟨p, (mx.2 p.val P.val).mpr ⟨p.property, P.property, qP⟩,
      Subtype.ext (value p (vt P.val hp q.val qP))⟩
  have subsets (D : B.Domain) (sub : B.MemberSubset D (e P)) : ∃ C : A.Domain, e C = D := by
    have bound : M.MemberSubset D.val P.val := by
      intro q hq
      let q' : B.Domain := ⟨q, yt D.val D.property q hq⟩
      exact eP ▸ ((my.2 q (e P).val).mp (sub q' ((my.2 q D.val).mpr ⟨q'.property, D.property, hq⟩))).2.2
    have hd := ry.subset_mem_l yt hVY hp D.property bound
    let C : A.Domain := ⟨D.val, xt V hVX D.val hd⟩
    exact ⟨C, Subtype.ext (value C hd)⟩
  obtain ⟨hG, f, injective, names, elementary⟩ := em_small_lift_l hA hB e elem O generic conditions subsets
  have ai : Function.Injective (Subtype.val : A.Domain → M.Domain) := fun _ _ eq => Subtype.ext eq
  have bi : Function.Injective (Subtype.val : B.Domain → M.Domain) := fun _ _ eq => Subtype.ext eq
  have af := smem_full_l I mx xt
  have bf := smem_full_l I my yt
  -- 共同传递层中的名字，连同每个带权子名字都有同一个原像。
  have entries (τ : A.Domain) (hτ : M.mem τ.val V) (s p : B.Domain) (sp : Entry_d B s p (e τ)) :
      ∃ a b : A.Domain, Entry_d A a b τ ∧ e a = s ∧ e b = p := by
    have raw : Entry_d M s.val p.val τ.val := value τ hτ ▸
      (image_entry_iff_l Subtype.val bi bf (KP.exists_pair (ZF.modelsKP hB)) hZF.1 s p (e τ)).mp sp
    have bounds := rd_entry_transitive_l vt hτ raw
    let a : A.Domain := ⟨s.val,xt V hVX s.val bounds.1⟩
    let b : A.Domain := ⟨p.val,xt V hVX p.val bounds.2⟩
    exact ⟨a,b,(image_entry_iff_l Subtype.val ai af (KP.exists_pair (ZF.modelsKP hA)) hZF.1 a b τ).mpr raw,
      Subtype.ext (value a bounds.1),Subtype.ext (value b bounds.2)⟩
  refine ⟨e, elem, values, hG, ?_, f, injective, names, elementary,?_⟩
  · intro q
    constructor
    · rintro ⟨p, hpU, rfl⟩
      have pP := ((mx.2 p.val P.val).mp (generic.proper p hpU).1).2.2
      exact ⟨p, hpU, (value p (vt P.val hp p.val pP)).symm⟩
    · rintro ⟨p, hpU, eq⟩
      have pP := ((mx.2 p.val P.val).mp (generic.proper p hpU).1).2.2
      exact ⟨p, hpU, Subtype.ext ((value p (vt P.val hp p.val pP)).trans eq)⟩
  · intro τ hτ x vx y
    constructor
    · intro hy
      obtain ⟨a,b,ab,hb,ay⟩ := (qval_mem_l (M := B) (em_order_l hA.1 hB.1 e elem O) hB hG (names τ x vx)).mp hy
      obtain ⟨a₀,b₀,old,ea,eb⟩ := entries τ hτ a b ab
      subst a b
      obtain ⟨b₁,hb₁,eq⟩ := hb
      have hb₀ : U b₀ := elem.injective_l hA.1 hB.1 eq ▸ hb₁
      obtain ⟨t,vt⟩ := name_value_l (M := A) (R := Q) (z := z) (U := U)
        ((em_name_l (M := A) (N := B) hA.1 hB.1 e elem).mpr (qval_name_l ay))
      exact ⟨t,(qval_mem_l (M := A) O hA generic vx).mpr ⟨a₀,b₀,old,hb₀,vt⟩,qval_unique_l (names a₀ t vt) ay⟩
    · rintro ⟨t,tx,rfl⟩
      exact (em_member_l (M := extension_l A hA P Q z U)
        (N := extension_l B hB (e P) (e Q) (e z) (Em_generic_d e U)) f elementary t x).mp tx

end Internal
end YesMetaZFC.SetTheory
