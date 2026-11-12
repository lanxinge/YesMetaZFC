import YesMetaZFC.Model.SetTheory.Source.Basic
import YesMetaZFC.Model.SetTheory.Internal.Quotient
import YesMetaZFC.SetTheory.InnerModel.Rudimentary.Construction
import YesMetaZFC.SetTheory.Collapse.RelationIso
import YesMetaZFC.SetTheory.Card.PowerFunction
import YesMetaZFC.Model.SetTheory.Internal.FunctionCode
import YesMetaZFC.Model.SetTheory.Embedding.PredicateTrace
import YesMetaZFC.SetTheory.InnerModel.Recursion.Composition
import YesMetaZFC.Model.SetTheory.Internal.Hereditary
import YesMetaZFC.SetTheory.Card.FiniteImage
import YesMetaZFC.SetTheory.KP.OrdinalCore
import YesMetaZFC.Model.SetTheory.Internal.CollectionCode

/-! # 原公式在任意编码关系模型中的相对化

成员关系读原关系图，量词限于原载体，定义原子也按该关系展开。
此解释不把商对象当作背景集合，不要求关系良基或载体传递。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention}

def rr_rel_m (𝒞 : OrderedPairConvention) : {n d : Nat} → Formula 1 n → Term d → Term d → (Fin n → Term d) → Formula 1 d
  | _, _, .falsum, _, _, _ => .falsum
  | _, _, .truth, _, _, _ => .truth
  | _, _, .mem s t, _, R, e => Formula.orderedPairMem 𝒞 (s.bind e) (t.bind e) R
  | _, _, .atom .extensionalEq _ ts, X, R, e => Formula.forallMem X
      (.iff (Formula.orderedPairMem 𝒞 .newest ((ts 0).bind e).weaken R.weaken)
        (Formula.orderedPairMem 𝒞 .newest ((ts 1).bind e).weaken R.weaken))
  | _, _, .atom .subset _ ts, X, R, e => Formula.forallMem X
      (.imp (Formula.orderedPairMem 𝒞 .newest ((ts 0).bind e).weaken R.weaken)
        (Formula.orderedPairMem 𝒞 .newest ((ts 1).bind e).weaken R.weaken))
  | _, _, .neg φ, X, R, e => .neg (rr_rel_m 𝒞 φ X R e)
  | _, _, .conj φ ψ, X, R, e => .conj (rr_rel_m 𝒞 φ X R e) (rr_rel_m 𝒞 ψ X R e)
  | _, _, .disj φ ψ, X, R, e => .disj (rr_rel_m 𝒞 φ X R e) (rr_rel_m 𝒞 ψ X R e)
  | _, _, .imp φ ψ, X, R, e => .imp (rr_rel_m 𝒞 φ X R e) (rr_rel_m 𝒞 ψ X R e)
  | _, _, .iff φ ψ, X, R, e => .iff (rr_rel_m 𝒞 φ X R e) (rr_rel_m 𝒞 ψ X R e)
  | _, _, .existsE φ, X, R, e => Formula.existsMem X
      (rr_rel_m 𝒞 φ X.weaken R.weaken (Fin.cases .newest (fun i => (e i).weaken)))
  | _, _, .forallE φ, X, R, e => Formula.forallMem X
      (rr_rel_m 𝒞 φ X.weaken R.weaken (Fin.cases .newest (fun i => (e i).weaken)))

@[simp] theorem rr_rel_closed_l (𝒞 : OrderedPairConvention) {n d} (φ : Formula 1 n) (hφ : φ.FreeClosed) (X R : Term d) (e : Fin n → Term d)
    (hX : X.freeSupport = []) (hR : R.freeSupport = []) (he : ∀ i, (e i).freeSupport = []) :
    (rr_rel_m 𝒞 φ X R e).FreeClosed := by
  induction φ generalizing d <;> simp only [Definitional.Formula.FreeClosed] at hφ
  case falsum | truth => trivial
  case mem s t =>
    simp only [rr_rel_m]
    exact Formula.orderedPairMem_freeClosed 𝒞 _ _ _
      ((Definitional.Term.freeSupport_bind_of_closed e he s).trans hφ.1)
      ((Definitional.Term.freeSupport_bind_of_closed e he t).trans hφ.2) hR
  case atom r hr ts =>
    have h0 := (Definitional.Term.freeSupport_bind_of_closed e he (ts 0)).trans (hφ 0)
    have h1 := (Definitional.Term.freeSupport_bind_of_closed e he (ts 1)).trans (hφ 1)
    cases r <;> simp -implicitDefEqProofs [rr_rel_m, Formula.forallMem, Definitional.Formula.FreeClosed, hX, hR, h0, h1]
  case neg φ ih => exact ih hφ X R e hX hR he
  case conj φ ψ ih jh | disj φ ψ ih jh | imp φ ψ ih jh | iff φ ψ ih jh =>
    exact ⟨ih hφ.1 X R e hX hR he, jh hφ.2 X R e hX hR he⟩
  case existsE φ ih | forallE φ ih =>
    exact ⟨⟨rfl, by simpa using hX⟩, ih hφ X.weaken R.weaken _ (by simpa using hX)
      (by simpa using hR) (Fin.cases rfl (fun i => by simpa using he i))⟩

theorem rr_rel_sat_l (I : 𝒞.Interpretation M) {X R : M.Domain}
    (nx : ∃ x, M.mem x X) {n d} (φ : Formula 1 n) (hφ : φ.FreeClosed)
    (ρ : Env (smdl_structure_l I (R := R) nx) n) (θ : Env M d) (T S : Term d) (e : Fin n → Term d)
    (hT : T.eval θ = X) (hS : S.eval θ = R) (he : ∀ i, (e i).eval θ = (ρ.bound i).val) :
    Formula.satisfies θ (rr_rel_m 𝒞 φ T S e) ↔ Formula.satisfies ρ φ := by
  have term {n d} (ρ : Env (smdl_structure_l I (R := R) nx) n) (θ : Env M d) (e : Fin n → Term d)
      (he : ∀ i, (e i).eval θ = (ρ.bound i).val) (t : Term n) (ht : t.freeSupport = []) :
      (t.bind e).eval θ = (t.eval ρ).val := by
    cases t with
    | free _ => simp at ht
    | bound i => exact he i
  induction φ generalizing d <;> simp only [Definitional.Formula.FreeClosed] at hφ
  case falsum | truth => simp only [rr_rel_m, Formula.satisfies_falsum_iff, Formula.satisfies_truth_iff]
  case mem s t =>
    simp only [rr_rel_m, Formula.satisfies_orderedPairMem_iff I, Formula.satisfies_mem_iff,
      term ρ θ e he s hφ.1, term ρ θ e he t hφ.2, hS]
    rfl
  case atom r hr ts =>
    cases r <;> simp only [rr_rel_m, Formula.satisfies_forallMem_iff, Formula.satisfies_iff_iff,
      Formula.satisfies_imp_iff, Formula.satisfies_orderedPairMem_iff I, Formula.satisfies_atom_extensionalEq_iff,
      Formula.satisfies_atom_subset_iff, Definitional.Term.eval_weaken, Definitional.Term.eval_newest,
      term ρ θ e he (ts 0) (hφ 0), term ρ θ e he (ts 1) (hφ 1), hT, hS]
    all_goals exact ⟨fun h x => h x.val x.property, fun h x hx => h ⟨x, hx⟩⟩
  case neg φ ih => exact not_congr (ih hφ ρ θ T S e hT hS he)
  case conj φ ψ ih jh | disj φ ψ ih jh | imp φ ψ ih jh | iff φ ψ ih jh =>
    simp only [rr_rel_m, Formula.satisfies_conj_iff, Formula.satisfies_disj_iff, Formula.satisfies_imp_iff,
      Formula.satisfies_iff_iff, ih hφ.1 ρ θ T S e hT hS he, jh hφ.2 ρ θ T S e hT hS he]
  case existsE φ ih | forallE φ ih =>
    have tr (x : (smdl_structure_l I (R := R) nx).Domain) := ih hφ (ρ.push x) (θ.push x.val) T.weaken S.weaken
      (Fin.cases .newest (fun i => (e i).weaken)) (by simpa using hT) (by simpa using hS)
      (Fin.cases rfl (fun i => (Definitional.Term.eval_weaken θ x.val (e i)).trans (he i)))
    first
    | rw [rr_rel_m, Formula.satisfies_existsMem_iff, Formula.satisfies_exists_iff, hT]
      exact ⟨fun ⟨x, hx, h⟩ => ⟨⟨x, hx⟩, (tr ⟨x, hx⟩).mp h⟩, fun ⟨x, h⟩ => ⟨x.val, x.property, (tr x).mpr h⟩⟩
    | rw [rr_rel_m, Formula.satisfies_forallMem_iff, Formula.satisfies_forall_iff, hT]
      exact ⟨fun h x => (tr x).mp (h x.val x.property), fun h x hx => (tr ⟨x, hx⟩).mpr (h ⟨x, hx⟩)⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 关系模型内部函数的实际坐标图

输入坐标图逐点进入内部定义域；函数仍由关系模型中的原对象给出。
背景替换只展开它的值，不把全部背景函数充作源内代表。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem smdl_extensional_l {c X R : M.Domain} (model : Smdl_d I c X R) (ext : Wc_ext_d X R) :
    Extensional (smdl_structure_l I (R := R) model.2.1) :=
  ⟨fun x y same => Subtype.ext (ext x.val x.property y.val y.property (fun z hz => same ⟨z, hz⟩))⟩

theorem smdl_function_l {X R D t : M.Domain} (nx : ∃ x, M.mem x X)
    (en : Extensional (smdl_structure_l I (R := R) nx))
    (d B f : (smdl_structure_l I (R := R) nx).Domain)
    (function : Fn0_d d B f) (ft : Fn0_d D X t)
    (domain : ∀ s x, Rd_entry_d s x t → Rd_entry_d x d.val R) :
    ∃ g, Fn0_d D X g ∧ ∀ s (x y : (smdl_structure_l I (R := R) nx).Domain),
      Rd_entry_d s x.val t → (Rd_entry_d s y.val g ↔ Rd_entry_d x y f) := by
  let N := smdl_structure_l I (R := R) nx
  let φ : Formula 1 3 := rd_entry0_m (.bound 1) .newest (.bound 2)
  have closed : φ.FreeClosed := by simp -implicitDefEqProofs [φ]
  let ρ : Env M 4 := ⟨Fin.cases f.val (Fin.cases t (Fin.cases R (fun _ => X))), fun _ => X⟩
  let ψ : BinarySchema 4 := {
    body := .conj (.mem .newest (.bound 5)) (Formula.existsMem (.bound 5)
      (.conj (rd_entry0_m (.bound 2) .newest (.bound 4))
        (rr_rel_m kpair_convention_l φ (.bound 6) (.bound 5) (Fin.cases (.bound 1) (Fin.cases .newest (fun _ => .bound 3))))))
    freeClosed := by
      simp only [Formula.existsMem, Definitional.Formula.FreeClosed]
      exact ⟨⟨rfl, rfl⟩, ⟨⟨rfl, rfl⟩, ⟨by simp -implicitDefEqProofs,
        rr_rel_closed_l kpair_convention_l φ closed _ _ _ rfl rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl)))⟩⟩⟩ }
  have bound s y (h : ψ.denote ρ s y) : M.mem y X := (Formula.satisfies_conj_iff ..).mp h |>.1
  have sat s (y : N.Domain) : ψ.denote ρ s y.val ↔
      ∃ x : N.Domain, Rd_entry_d s x.val t ∧ Rd_entry_d x y f := by
    simp only [ψ, BinarySchema.denote, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
      rd_entry0_sat_l hZF.1, Formula.satisfies_mem_iff]
    have decode (x : N.Domain) := (rr_rel_sat_l I nx φ closed
      ⟨Fin.cases y (Fin.cases x (fun _ => f)), fun _ => f⟩ (((ρ.push s).push y.val).push x.val)
      (.bound 6) (.bound 5) (Fin.cases (.bound 1) (Fin.cases .newest (fun _ => .bound 3)))
      rfl rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl)))).trans (rd_entry0_sat_l en ..)
    exact ⟨fun ⟨_, x, hx, hsx, h⟩ => ⟨⟨x, hx⟩, hsx, (decode ⟨x, hx⟩).mp h⟩,
      fun ⟨x, hsx, h⟩ => ⟨y.property, x.val, x.property, hsx, (decode x).mpr h⟩⟩
  obtain ⟨g, fg, spec⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I ψ ρ (source := D) (target := X)
    (fun s hs => by
      obtain ⟨x, hx, hsx⟩ := ft.2.1 s hs
      obtain ⟨y, _, hxy⟩ := function.2.1 ⟨x, hx⟩ (domain s x hsx)
      exact ⟨y.val, (sat s y).mpr ⟨⟨x, hx⟩, hsx, hxy⟩⟩)
    (fun s _ y z hy hz => by
      obtain ⟨x, hsx, hxy⟩ := (sat s ⟨y, bound s y hy⟩).mp hy
      obtain ⟨x', hsx', hxz⟩ := (sat s ⟨z, bound s z hz⟩).mp hz
      have eq : x = x' := Subtype.ext ((fn0_function_l (ZF.modelsKP hZF) ft).1.2 s x.val x'.val hsx hsx')
      exact congrArg Subtype.val (function.2.2 x (domain s x.val hsx) _ (function.bound_l hxy).2
        _ (function.bound_l hxz).2 hxy (eq.symm ▸ hxz)))
    (fun s y _ h => bound s y h)
  refine ⟨g, fn0_of_function_l (ZF.modelsKP hZF) fg, ?_⟩
  intro s x y hsx
  refine (spec s y.val).trans ((and_congr_right fun _ => sat s y).trans ⟨?_, ?_⟩)
  · rintro ⟨_, x', hsx', h⟩
    have eq : x' = x := Subtype.ext ((fn0_function_l (ZF.modelsKP hZF) ft).1.2 s x'.val x.val hsx' hsx)
    exact eq ▸ h
  · exact fun h => ⟨(ft.bound_l hsx).1, x, hsx, h⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 原关系模型中幂集值函数的外部计数

先把内部单射展开为实际载体之间的集合单射，再对原模型自己的函数空间
应用子集编码。只计数内部函数，不将背景中的任意函数混入代表族。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 内部单射给出两份实际关系载体之间的单射。 -/
theorem rr_cardinal_bound_l {X R A B : M.Domain} (nx : ∃ x, M.mem x X)
    (hN : (smdl_structure_l I (R := R) nx).Models KP)
    (a b : (smdl_structure_l I (R := R) nx).Domain)
    (source : ∀ x, M.mem x A ↔ M.mem x X ∧ Rd_entry_d x a.val R)
    (target : ∀ x, M.mem x B ↔ M.mem x X ∧ Rd_entry_d x b.val R)
    (bound : (smdl_structure_l I (R := R) nx).CardinalLessOrEqual (kp_pair_l hN) a b) :
    M.CardinalLessOrEqual I A B := by
  let N := smdl_structure_l I (R := R) nx
  obtain ⟨f,ff⟩ := bound
  obtain ⟨t,ft⟩ := ZF.exists_identityBijection hZF I A
  have coord := (fn0_of_function_l (ZF.modelsKP hZF) ft.1.1).mono_target_l
    (fun x hx => ((source x).mp hx).1)
  have domain s x (sx : Rd_entry_d s x t) : Rd_entry_d x a.val R :=
    ((source x).mp (ft.1.1.output_mem_of_pairMember sx)).2
  obtain ⟨g,fg,read⟩ := smdl_function_l hZF nx hN.1 a b f
    (fn0_of_function_l hN ff.1) coord domain
  have values s y (sy : Rd_entry_d s y g) : M.mem y B := by
    obtain ⟨x,hx,sx⟩ := coord.2.1 s (fg.bound_l sy).1
    exact (target y).mpr ⟨(fg.bound_l sy).2,
      ff.1.output_mem_of_pairMember ((read s ⟨x,hx⟩ ⟨y,(fg.bound_l sy).2⟩ sx).mp sy)⟩
  refine ⟨g,fn0_function_l (ZF.modelsKP hZF) (fg.retarget_l values),?_⟩
  intro s s' y sy sy'
  obtain ⟨x,hx,sx⟩ := coord.2.1 s (fg.bound_l sy).1
  obtain ⟨x',hx',sx'⟩ := coord.2.1 s' (fg.bound_l sy').1
  have eq : (⟨x,hx⟩ : N.Domain) = ⟨x',hx'⟩ := ff.2 _ _ _
    ((read s ⟨x,hx⟩ ⟨y,(fg.bound_l sy).2⟩ sx).mp sy)
    ((read s' ⟨x',hx'⟩ ⟨y,(fg.bound_l sy').2⟩ sx').mp sy')
  have same : x' = x := congrArg Subtype.val eq.symm
  exact ft.1.2 s s' x sx (show Rd_entry_d s' x t from same ▸ sx')

/-- 原幂集载体可数，便足以枚举全部原生的小定义域幂集值函数。 -/
theorem rr_power_function_count_l {X R Ω B : M.Domain} (nx : ∃ x, M.mem x X)
    (native : (smdl_structure_l I (R := R) nx).Models ZF)
    (ω δ d P : (smdl_structure_l I (R := R) nx).Domain)
    (hω : (smdl_structure_l I (R := R) nx).IsOmega ω)
    (hδ : (smdl_structure_l I (R := R) nx).IsInfiniteCardinal (kp_pair_l (ZF.modelsKP native)) ω δ)
    (small : (smdl_structure_l I (R := R) nx).CardinalLessOrEqual (kp_pair_l (ZF.modelsKP native)) d δ)
    (power : (smdl_structure_l I (R := R) nx).IsPowerSetOf P δ)
    (carrier : ∀ x, M.mem x B ↔ M.mem x X ∧ Rd_entry_d x P.val R)
    (count : M.CardinalLessOrEqual I B Ω) :
    ∃ F : (smdl_structure_l I (R := R) nx).Domain, ∃ C,
      (smdl_structure_l I (R := R) nx).IsFunctionSpace (kp_pair_l (ZF.modelsKP native)) F d P ∧
      (∀ x, M.mem x C ↔ M.mem x X ∧ Rd_entry_d x F.val R) ∧ M.CardinalLessOrEqual I C Ω := by
  obtain ⟨F,space⟩ := ZF.exists_functionSpace native (kp_pair_l (ZF.modelsKP native)) d P
  let φ : UnarySchema 2 := { body := rd_entry0_m .newest (.bound 1) (.bound 2) }
  obtain ⟨C,hC⟩ := ZF.separation_exists_d hZF φ ⟨Fin.cases F.val (fun _ => R),fun _ => X⟩ X
  have source x : M.mem x C ↔ M.mem x X ∧ Rd_entry_d x F.val R :=
    (hC x).trans (and_congr_right fun _ => rd_entry0_sat_l hZF.1 ..)
  obtain ⟨j,hj⟩ := rr_cardinal_bound_l hZF nx (ZF.modelsKP native) F P source carrier
    (ZF.power_function_bound_l (kp_pair_l (ZF.modelsKP native)) native hω hδ small power space)
  obtain ⟨k,hk⟩ := count
  exact ⟨F,C,space,source,ZF.exists_compositionInjection hZF I hj hk⟩

/-- 幂集可数自动控制其底集中的序数；扩展器支撑据此计数。 -/
theorem rr_power_ordinal_count_l {X R Ω B L : M.Domain} (nx : ∃ x, M.mem x X)
    (native : (smdl_structure_l I (R := R) nx).Models ZF)
    (δ ℓ P : (smdl_structure_l I (R := R) nx).Domain)
    (ordinal : (smdl_structure_l I (R := R) nx).IsOrdinal δ)
    (below : (smdl_structure_l I (R := R) nx).mem ℓ δ)
    (power : (smdl_structure_l I (R := R) nx).IsPowerSetOf P δ)
    (carrier : ∀ x, M.mem x B ↔ M.mem x X ∧ Rd_entry_d x P.val R)
    (count : M.CardinalLessOrEqual I B Ω)
    (length : ∀ x, M.mem x L ↔ M.mem x X ∧ Rd_entry_d x ℓ.val R) :
    M.CardinalLessOrEqual I L Ω := by
  let J := kp_pair_l (ZF.modelsKP native)
  obtain ⟨i,hi⟩ := ZF.exists_inclusionInjection native J (ordinal.transitive ℓ below)
  obtain ⟨j,hj⟩ := ZF.exists_singletonInjectionToPowerSet native J power
  obtain ⟨k,hk⟩ := rr_cardinal_bound_l hZF nx (ZF.modelsKP native) ℓ P length carrier
    (ZF.exists_compositionInjection native J hi hj)
  obtain ⟨e,he⟩ := count
  exact ZF.exists_compositionInjection hZF I hk he

end YesMetaZFC.SetTheory.Internal

/-! ## 原关系中的函数码与求值

函数性和求值均解释为原关系模型中的固定公式；背景只存放对象码。
关系外延性用来读取函数的单值性，传递性仅用于识别旧隶属模型的函数图。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Rf_ext_d (X R : M.Domain) : Prop := ∀ x, M.mem x X → ∀ y, M.mem y X →
  (∀ z, M.mem z X → (M.PairMember I z x R ↔ M.PairMember I z y R)) → x = y

def rf_ext_m {d} (X R : Term d) : Formula 1 d := Formula.forallMem X
  (Formula.forallMem X.weaken (.imp (Formula.forallMem X.weaken.weaken
    (.iff (Formula.orderedPairMem 𝒞 .newest (.bound 2) R.weaken.weaken.weaken)
      (Formula.orderedPairMem 𝒞 .newest (.bound 1) R.weaken.weaken.weaken)))
    (Formula.extensionalEq (.bound 1) .newest)))
derive_free_closed rf_ext_m

theorem rf_ext_sat_l (hE : Extensional M) {d} (ρ : Env M d) (X R : Term d) :
    Formula.satisfies ρ (rf_ext_m (𝒞 := 𝒞) X R) ↔ Rf_ext_d I (X.eval ρ) (R.eval ρ) := by
  simp only [rf_ext_m, Rf_ext_d, Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_iff_iff, Formula.satisfies_orderedPairMem_iff I,
    Formula.satisfies_extensionalEq_iff_eq hE, Definitional.Term.eval_weaken]; rfl

theorem Rf_ext_d.native_l {X R} (h : Rf_ext_d I X R) (nx : ∃ x, M.mem x X) :
    Extensional (smdl_structure_l I (R := R) nx) :=
  ⟨fun x y same => Subtype.ext (h x.val x.property y.val y.property (fun z hz => same ⟨z, hz⟩))⟩

theorem rf_ext_mem_l (hE : Extensional M) {c X R} (hX : M.TransitiveSet X) (hm : Smem_d I c X R) :
    Rf_ext_d I X R := by
  intro x hx y hy same
  apply hE.eq_of_same_members x y
  intro z
  exact ⟨fun hz => ((hm.2 z y).mp ((same z (hX x hx z hz)).mp ((hm.2 z x).mpr ⟨hX x hx z hz, hx, hz⟩))).2.2,
    fun hz => ((hm.2 z x).mp ((same z (hX y hy z hz)).mpr ((hm.2 z y).mpr ⟨hX y hy z hz, hy, hz⟩))).2.2⟩

def Rf_val_d (X R p x f : M.Domain) : Prop := ∃ hp : M.mem p X, ∃ hx : M.mem x X, ∃ hf : M.mem f X,
  Formula.satisfies (⟨Fin.cases ⟨p, hp⟩ (Fin.cases ⟨x, hx⟩ (fun _ => ⟨f, hf⟩)), fun _ => ⟨f, hf⟩⟩ :
    Env (smdl_structure_l I (R := R) ⟨f, hf⟩) 3) (rd_entry0_m .newest (.bound 1) (.bound 2))

def Rf_fun_d (X R D f : M.Domain) : Prop := ∃ hD : M.mem D X, ∃ hf : M.mem f X,
  ∃ B : (smdl_structure_l I (R := R) ⟨D, hD⟩).Domain,
    Formula.satisfies (⟨Fin.cases ⟨D, hD⟩ (Fin.cases B (fun _ => ⟨f, hf⟩)), fun _ => ⟨f, hf⟩⟩ :
      Env (smdl_structure_l I (R := R) ⟨D, hD⟩) 3) (fn0_m .newest (.bound 1) (.bound 2))

def rf_val_m {d} (X R p x f : Term d) : Formula 1 d :=
  .conj (.mem p X) (.conj (.mem x X) (.conj (.mem f X)
    (rr_rel_m 𝒞 (n := 3) (rd_entry0_m .newest (.bound 1) (.bound 2)) X R (Fin.cases p (Fin.cases x (fun _ => f))))))

def rf_fun_m {d} (X R D f : Term d) : Formula 1 d :=
  .conj (.mem D X) (.conj (.mem f X) (Formula.existsMem X
    (rr_rel_m 𝒞 (n := 3) (fn0_m .newest (.bound 1) (.bound 2)) X.weaken R.weaken
      (Fin.cases D.weaken (Fin.cases .newest (fun _ => f.weaken))))))

@[simp] theorem rf_val_closed_l {d} (X R p x f : Term d) (hX : X.freeSupport = [])
    (hR : R.freeSupport = []) (hp : p.freeSupport = []) (hx : x.freeSupport = []) (hf : f.freeSupport = []) :
    (rf_val_m (𝒞 := 𝒞) X R p x f).FreeClosed := by
  exact ⟨⟨hp, hX⟩, ⟨⟨hx, hX⟩, ⟨⟨hf, hX⟩, rr_rel_closed_l 𝒞 _ (by simp -implicitDefEqProofs)
    X R _ hX hR (Fin.cases hp (Fin.cases hx (fun _ => hf)))⟩⟩⟩

@[simp] theorem rf_fun_closed_l {d} (X R D f : Term d) (hX : X.freeSupport = [])
    (hR : R.freeSupport = []) (hD : D.freeSupport = []) (hf : f.freeSupport = []) :
    (rf_fun_m (𝒞 := 𝒞) X R D f).FreeClosed := by
  exact ⟨⟨hD, hX⟩, ⟨⟨hf, hX⟩, ⟨⟨rfl, by simpa using hX⟩,
    rr_rel_closed_l 𝒞 _ (by simp -implicitDefEqProofs) _ _ _ (by simpa using hX) (by simpa using hR)
      (Fin.cases (by simpa using hD) (Fin.cases rfl (fun _ => by simpa using hf)))⟩⟩⟩

theorem rf_val_sat_l {d} (ρ : Env M d) (X R p x f : Term d) :
    Formula.satisfies ρ (rf_val_m (𝒞 := 𝒞) X R p x f) ↔
      Rf_val_d I (X.eval ρ) (R.eval ρ) (p.eval ρ) (x.eval ρ) (f.eval ρ) := by
  have read (hp : M.mem (p.eval ρ) (X.eval ρ)) (hx : M.mem (x.eval ρ) (X.eval ρ))
      (hf : M.mem (f.eval ρ) (X.eval ρ)) := rr_rel_sat_l I (R := R.eval ρ) ⟨f.eval ρ, hf⟩
    (rd_entry0_m (n := 3) .newest (.bound 1) (.bound 2)) (by simp -implicitDefEqProofs)
    (⟨Fin.cases ⟨p.eval ρ, hp⟩ (Fin.cases ⟨x.eval ρ, hx⟩ (fun _ => ⟨f.eval ρ, hf⟩)), fun _ => ⟨f.eval ρ, hf⟩⟩)
    ρ X R (Fin.cases p (Fin.cases x (fun _ => f))) rfl rfl
    (Fin.cases rfl (Fin.cases rfl (fun _ => rfl)))
  change (_ ∧ _ ∧ _ ∧ _) ↔ ∃ hp hx hf, _
  exact ⟨fun ⟨hp, hx, hf, h⟩ => ⟨hp, hx, hf, (read hp hx hf).mp h⟩,
    fun ⟨hp, hx, hf, h⟩ => ⟨hp, hx, hf, (read hp hx hf).mpr h⟩⟩

theorem rf_fun_sat_l {d} (ρ : Env M d) (X R D f : Term d) :
    Formula.satisfies ρ (rf_fun_m (𝒞 := 𝒞) X R D f) ↔
      Rf_fun_d I (X.eval ρ) (R.eval ρ) (D.eval ρ) (f.eval ρ) := by
  have read (hD : M.mem (D.eval ρ) (X.eval ρ)) (hf : M.mem (f.eval ρ) (X.eval ρ))
      (B : M.Domain) (hB : M.mem B (X.eval ρ)) := rr_rel_sat_l I (R := R.eval ρ) ⟨D.eval ρ, hD⟩
    (fn0_m (n := 3) .newest (.bound 1) (.bound 2)) (by simp -implicitDefEqProofs)
    (⟨Fin.cases ⟨D.eval ρ, hD⟩ (Fin.cases ⟨B, hB⟩ (fun _ => ⟨f.eval ρ, hf⟩)), fun _ => ⟨f.eval ρ, hf⟩⟩)
    (ρ.push B) X.weaken R.weaken (Fin.cases D.weaken (Fin.cases .newest (fun _ => f.weaken)))
    (by simp only [Definitional.Term.eval_weaken]) (by simp only [Definitional.Term.eval_weaken])
    (Fin.cases (Definitional.Term.eval_weaken ρ B D)
      (Fin.cases rfl (fun _ => Definitional.Term.eval_weaken ρ B f)))
  simp only [rf_fun_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_existsMem_iff, Rf_fun_d]
  exact ⟨fun ⟨hD, hf, B, hB, h⟩ => ⟨hD, hf, ⟨B, hB⟩, (read hD hf B hB).mp h⟩,
    fun ⟨hD, hf, B, h⟩ => ⟨hD, hf, B.val, B.property, (read hD hf B.val B.property).mpr h⟩⟩

theorem rf_val_native_l {X R} (nx : ∃ x, M.mem x X) (ext : Extensional (smdl_structure_l I (R := R) nx))
    (p x f : (smdl_structure_l I (R := R) nx).Domain) :
    Rf_val_d I X R p.val x.val f.val ↔ Rd_entry_d p x f := by
  exact ⟨fun ⟨_, _, _, h⟩ => (rd_entry0_sat_l ext ..).mp h,
    fun h => ⟨p.property, x.property, f.property, (rd_entry0_sat_l ext ..).mpr h⟩⟩

theorem rf_fun_native_l {X R} (nx : ∃ x, M.mem x X) (ext : Extensional (smdl_structure_l I (R := R) nx))
    (D f : (smdl_structure_l I (R := R) nx).Domain) :
    Rf_fun_d I X R D.val f.val ↔ ∃ B : (smdl_structure_l I (R := R) nx).Domain, Fn0_d D B f := by
  exact ⟨fun ⟨_, _, B, h⟩ => ⟨B, (fn0_sat_l ext ..).mp h⟩,
    fun ⟨B, h⟩ => ⟨D.property, f.property, B, (fn0_sat_l ext ..).mpr h⟩⟩

theorem rf_val_mem_l (hE : Extensional M) {c X R p x f} (hX : M.TransitiveSet X)
    (hm : Smem_d I c X R) (hf : M.mem f X) : Rf_val_d I X R p x f ↔ Rd_entry_d p x f := by
  have read hp hx := (smem_delta_image_l I hm hX (rd_entry0_delta_l .newest (.bound 1) (.bound 2))
    (⟨Fin.cases ⟨p, hp⟩ (Fin.cases ⟨x, hx⟩ (fun _ => ⟨f, hf⟩)), fun _ => ⟨f, hf⟩⟩ :
      Env (smdl_structure_l I (R := R) hm.1.2.1) 3)).trans (rd_entry0_sat_l hE _ .newest (.bound 1) (.bound 2))
  exact ⟨fun ⟨hp, hx, _, h⟩ => (read hp hx).mp h, fun h =>
    ⟨(rd_entry_transitive_l hX hf h).1, (rd_entry_transitive_l hX hf h).2, hf, (read _ _).mpr h⟩⟩

theorem rf_fun_mem_l (hE : Extensional M) {c X R D f} (hX : M.TransitiveSet X)
    (hm : Smem_d I c X R) (hD : M.mem D X) : Rf_fun_d I X R D f ↔ Sfun_d X D f := by
  have read hf (B : (smdl_structure_l I (R := R) hm.1.2.1).Domain) :=
    (smem_delta_image_l I hm hX (fn0_delta_l .newest (.bound 1) (.bound 2))
      (⟨Fin.cases ⟨D, hD⟩ (Fin.cases B (fun _ => ⟨f, hf⟩)), fun _ => ⟨f, hf⟩⟩ :
        Env (smdl_structure_l I (R := R) hm.1.2.1) 3)).trans (fn0_sat_l hE _ .newest (.bound 1) (.bound 2))
  exact ⟨fun ⟨_, hf, B, h⟩ => ⟨hf, B.val, B.property, (read hf B).mp h⟩,
    fun ⟨hf, B, hB, h⟩ => ⟨hD, hf, ⟨B, hB⟩, (read hf ⟨B, hB⟩).mpr h⟩⟩

theorem Rf_fun_d.mem_l {X R D f} (h : Rf_fun_d I X R D f) : M.mem f X :=
  h.elim fun _ h => h.elim fun hf _ => hf

theorem Rf_val_d.bounds_l {X R p x f} (h : Rf_val_d I X R p x f) : M.mem p X ∧ M.mem x X ∧ M.mem f X :=
  h.elim fun hp h => h.elim fun hx h => h.elim fun hf _ => ⟨hp, hx, hf⟩

theorem Rf_fun_d.value_l {X R D f p} (h : Rf_fun_d I X R D f) (ext : Rf_ext_d I X R)
    (hp : M.mem p X) (hd : M.PairMember I p D R) : ∃ x, Rf_val_d I X R p x f := by
  obtain ⟨hD, hf, B, funsat⟩ := h
  have en := ext.native_l I ⟨D, hD⟩
  have fn := (fn0_sat_l en _ .newest (.bound 1) (.bound 2)).mp funsat
  obtain ⟨x, _, hx⟩ := fn.2.1 ⟨p, hp⟩ hd
  exact ⟨x.val, (rf_val_native_l I ⟨D, hD⟩ en ⟨p, hp⟩ x ⟨f, hf⟩).mpr hx⟩

theorem Rf_fun_d.unique_l {X R D f p x y} (h : Rf_fun_d I X R D f) (ext : Rf_ext_d I X R)
    (hx : Rf_val_d I X R p x f) (hy : Rf_val_d I X R p y f) : x = y := by
  obtain ⟨hD, hf, B, funsat⟩ := h
  have en := ext.native_l I ⟨D, hD⟩
  have fn := (fn0_sat_l en _ .newest (.bound 1) (.bound 2)).mp funsat
  have px := (rf_val_native_l I ⟨D, hD⟩ en ⟨p, hx.bounds_l I |>.1⟩ ⟨x, hx.bounds_l I |>.2.1⟩ ⟨f, hf⟩).mp hx
  have py := (rf_val_native_l I ⟨D, hD⟩ en ⟨p, hy.bounds_l I |>.1⟩ ⟨y, hy.bounds_l I |>.2.1⟩ ⟨f, hf⟩).mp hy
  exact congrArg Subtype.val (fn.2.2 _ (fn.bound_l px).1 _ (fn.bound_l px).2 _ (fn.bound_l py).2 px py)

end YesMetaZFC.SetTheory.Internal

/-! ## 原关系函数对象及其值沿实际初等图的像

量词保留在原关系模型中；值域对象也由同一图实际取得。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M) (hZF : M.Models ZF)
include hZF

theorem Rf_fun_d.map_l {ω c d X R Y S j D D' f f' : M.Domain}
    (hω : M.IsOmega ω) (mx : Smdl_d I c X R) (my : Smdl_d I d Y S) (map : Smap_d I ω c d X Y j)
    (hD : M.PairMember I D D' j) (hf : M.PairMember I f f' j) (fn : Rf_fun_d I X R D f) :
    Rf_fun_d I Y S D' f' := by
  obtain ⟨hd, hf₀, B, valid⟩ := fn
  obtain ⟨B', hB', hb⟩ := map.1.1.2.2 B.val B.property
  have hd' := map.1.1.output_mem_of_pairMember hD
  have hf' := map.1.1.output_mem_of_pairMember hf
  let ρ : Env (smdl_structure_l I (R := R) mx.2.1) 3 :=
    ⟨Fin.cases ⟨D, hd⟩ (Fin.cases B (fun _ => ⟨f, hf₀⟩)), fun _ => ⟨f, hf₀⟩⟩
  let η : Env (smdl_structure_l I (R := S) my.2.1) 3 :=
    ⟨Fin.cases ⟨D', hd'⟩ (Fin.cases ⟨B', hB'⟩ (fun _ => ⟨f', hf'⟩)), fun _ => ⟨f', hf'⟩⟩
  exact ⟨hd', hf', ⟨B', hB'⟩, (smap_source_l I hZF hω mx my map
    (fn0_m .newest (.bound 1) (.bound 2)) (by simp -implicitDefEqProofs) ρ η
    (Fin.cases hD (Fin.cases hb (fun _ => hf)))).mp valid⟩

theorem Rf_val_d.map_l {ω c d X R Y S j p p' x x' f f' : M.Domain}
    (hω : M.IsOmega ω) (mx : Smdl_d I c X R) (my : Smdl_d I d Y S) (map : Smap_d I ω c d X Y j)
    (hp : M.PairMember I p p' j) (hx : M.PairMember I x x' j) (hf : M.PairMember I f f' j)
    (value : Rf_val_d I X R p x f) : Rf_val_d I Y S p' x' f' := by
  obtain ⟨hp₀, hx₀, hf₀, valid⟩ := value
  have hp' := map.1.1.output_mem_of_pairMember hp
  have hx' := map.1.1.output_mem_of_pairMember hx
  have hf' := map.1.1.output_mem_of_pairMember hf
  let ρ : Env (smdl_structure_l I (R := R) mx.2.1) 3 :=
    ⟨Fin.cases ⟨p, hp₀⟩ (Fin.cases ⟨x, hx₀⟩ (fun _ => ⟨f, hf₀⟩)), fun _ => ⟨f, hf₀⟩⟩
  let η : Env (smdl_structure_l I (R := S) my.2.1) 3 :=
    ⟨Fin.cases ⟨p', hp'⟩ (Fin.cases ⟨x', hx'⟩ (fun _ => ⟨f', hf'⟩)), fun _ => ⟨f', hf'⟩⟩
  exact ⟨hp', hx', hf', (smap_source_l I hZF hω mx my map
    (rd_entry0_m .newest (.bound 1) (.bound 2)) (by simp -implicitDefEqProofs) ρ η
    (Fin.cases hp (Fin.cases hx (fun _ => hf)))).mp valid⟩

/-- 给定同一原图上的三个实际像，函数求值也可由目标直接回拉。 -/
theorem Rf_val_d.pull_l {ω c d X R Y S j p p' x x' f f' : M.Domain}
    (hω : M.IsOmega ω) (mx : Smdl_d I c X R) (my : Smdl_d I d Y S) (map : Smap_d I ω c d X Y j)
    (hp : M.PairMember I p p' j) (hx : M.PairMember I x x' j) (hf : M.PairMember I f f' j)
    (value : Rf_val_d I Y S p' x' f') : Rf_val_d I X R p x f := by
  obtain ⟨hp',hx',hf',valid⟩ := value
  have hp₀ := map.1.1.input_mem_of_pairMember hp
  have hx₀ := map.1.1.input_mem_of_pairMember hx
  have hf₀ := map.1.1.input_mem_of_pairMember hf
  let ρ : Env (smdl_structure_l I (R := R) mx.2.1) 3 :=
    ⟨Fin.cases ⟨p,hp₀⟩ (Fin.cases ⟨x,hx₀⟩ (fun _ => ⟨f,hf₀⟩)),fun _ => ⟨f,hf₀⟩⟩
  let η : Env (smdl_structure_l I (R := S) my.2.1) 3 :=
    ⟨Fin.cases ⟨p',hp'⟩ (Fin.cases ⟨x',hx'⟩ (fun _ => ⟨f',hf'⟩)),fun _ => ⟨f',hf'⟩⟩
  exact ⟨hp₀,hx₀,hf₀,(smap_source_l I hZF hω mx my map
    (rd_entry0_m .newest (.bound 1) (.bound 2)) (by simp -implicitDefEqProofs) ρ η
    (Fin.cases hp (Fin.cases hx (fun _ => hf)))).mpr valid⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 原模型函数在全部对象码上的实际图

先分离内部定义域与值域的全部对象码，再以原函数的求值公式作替换。
原函数和新集合图逐点等价，无须传递源或共同低层。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem smdl_graph_l {X R : M.Domain} (nx : ∃ x, M.mem x X)
    (ext : Extensional (smdl_structure_l I (R := R) nx))
    (d a f : (smdl_structure_l I (R := R) nx).Domain) (fn : Fn0_d d a f) :
    ∃ D A g, (∀ x, M.mem x D ↔ M.mem x X ∧ Rd_entry_d x d.val R) ∧
      (∀ x, M.mem x A ↔ M.mem x X ∧ Rd_entry_d x a.val R) ∧ Fn0_d D A g ∧
      ∀ x y : (smdl_structure_l I (R := R) nx).Domain, Rd_entry_d x.val y.val g ↔ Rd_entry_d x y f := by
  let N := smdl_structure_l I (R := R) nx
  let χ : UnarySchema 2 := { body := rd_entry0_m .newest (.bound 1) (.bound 2) }
  have carrier (a : N.Domain) : ∃ A, ∀ x, M.mem x A ↔ M.mem x X ∧ Rd_entry_d x a.val R := by
    obtain ⟨A, spec⟩ := ZF.separation_exists_d hZF χ ⟨Fin.cases a.val (fun _ => R), fun _ => X⟩ X
    exact ⟨A, fun x => (spec x).trans (and_congr_right fun _ => rd_entry0_sat_l hZF.1 ..)⟩
  obtain ⟨D, cd⟩ := carrier d
  obtain ⟨A, ca⟩ := carrier a
  let ρ : Env M 3 := ⟨Fin.cases f.val (Fin.cases R (fun _ => X)), fun _ => X⟩
  let φ : BinarySchema 3 := {
    body := rf_val_m (𝒞 := kpair_convention_l) (.bound 4) (.bound 3) (.bound 1) .newest (.bound 2) }
  have sat x y : φ.denote ρ x y ↔ Rf_val_d I X R x y f.val := rf_val_sat_l I ..
  have read (x y : N.Domain) : φ.denote ρ x.val y.val ↔ Rd_entry_d x y f :=
    (sat x.val y.val).trans (rf_val_native_l I nx ext x y f)
  obtain ⟨g, fg, spec⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := D) (target := A)
    (fun x hx => by
      obtain ⟨y, _, hxy⟩ := fn.2.1 ⟨x, ((cd x).mp hx).1⟩ ((cd x).mp hx).2
      exact ⟨y.val, (read ⟨x, ((cd x).mp hx).1⟩ y).mpr hxy⟩)
    (fun x hx y z hy hz => by
      let x' : N.Domain := ⟨x, ((cd x).mp hx).1⟩
      let y' : N.Domain := ⟨y, (((sat x y).mp hy).bounds_l I).2.1⟩
      let z' : N.Domain := ⟨z, (((sat x z).mp hz).bounds_l I).2.1⟩
      have hy' := (read x' y').mp hy
      have hz' := (read x' z').mp hz
      exact congrArg Subtype.val (fn.2.2 x' ((cd x).mp hx).2 y' (fn.bound_l hy').2
        z' (fn.bound_l hz').2 hy' hz'))
    (fun x y hx hy => by
      let x' : N.Domain := ⟨x, ((cd x).mp hx).1⟩
      let y' : N.Domain := ⟨y, (((sat x y).mp hy).bounds_l I).2.1⟩
      exact (ca y).mpr ⟨y'.property, (fn.bound_l ((read x' y').mp hy)).2⟩)
  refine ⟨D, A, g, cd, ca, fn0_of_function_l (ZF.modelsKP hZF) fg, fun x y => ?_⟩
  exact (spec x.val y.val).trans ((and_congr_right fun _ => read x y).trans
    ⟨And.right, fun h => ⟨(cd x.val).mpr ⟨x.property, (fn.bound_l h).1⟩, h⟩⟩)

end YesMetaZFC.SetTheory.Internal

/-! ## 原函数展开图的恒等和复合

对象码载体精确包含原定义域的成员，展开图逐项读取原函数值。因此原
函数的恒等、复合方程直接成为背景实际图的方程，不选择新代表。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem smdl_graph_identity_l {N R D t : M.Domain} (nx : ∃ x, M.mem x N)
    (d p : (smdl_structure_l I (R := R) nx).Domain)
    (dc : ∀ x, M.mem x D ↔ M.mem x N ∧ M.PairMember I x d.val R)
    (ft : Fn0_d D D t)
    (graph : ∀ x y : (smdl_structure_l I (R := R) nx).Domain, Rd_entry_d x.val y.val t ↔ Rd_entry_d x y p)
    (identity : ∀ x y, Rd_entry_d x y p ↔ (smdl_structure_l I (R := R) nx).mem x d ∧ x = y) :
    ∀ x y, Rd_entry_d x y t ↔ M.mem x D ∧ x = y := by
  intro x y
  constructor
  · intro h
    let x' : (smdl_structure_l I (R := R) nx).Domain := ⟨x, ((dc x).mp (ft.bound_l h).1).1⟩
    let y' : (smdl_structure_l I (R := R) nx).Domain := ⟨y, ((dc y).mp (ft.bound_l h).2).1⟩
    exact ⟨(ft.bound_l h).1, congrArg Subtype.val ((identity x' y').mp ((graph x' y').mp h)).2⟩
  · rintro ⟨hx, rfl⟩
    let x' : (smdl_structure_l I (R := R) nx).Domain := ⟨x, ((dc x).mp hx).1⟩
    exact (graph x' x').mpr ((identity x' x').mpr ⟨((dc x).mp hx).2, rfl⟩)

theorem smdl_graph_composition_l {N R A B C f g h : M.Domain} (nx : ∃ x, M.mem x N)
    (a b c p q r : (smdl_structure_l I (R := R) nx).Domain)
    (ac : ∀ x, M.mem x A ↔ M.mem x N ∧ M.PairMember I x a.val R)
    (bc : ∀ x, M.mem x B ↔ M.mem x N ∧ M.PairMember I x b.val R)
    (cc : ∀ x, M.mem x C ↔ M.mem x N ∧ M.PairMember I x c.val R)
    (fh : Fn0_d C A h)
    (gp : ∀ x y : (smdl_structure_l I (R := R) nx).Domain, Rd_entry_d x.val y.val f ↔ Rd_entry_d x y p)
    (gq : ∀ x y : (smdl_structure_l I (R := R) nx).Domain, Rd_entry_d x.val y.val g ↔ Rd_entry_d x y q)
    (gr : ∀ x y : (smdl_structure_l I (R := R) nx).Domain, Rd_entry_d x.val y.val h ↔ Rd_entry_d x y r)
    (comp : Cp0_d c b a q p r) : Cp0_d C B A g f h := by
  refine ⟨fh, fun x hx => ?_⟩
  let x' : (smdl_structure_l I (R := R) nx).Domain := ⟨x, ((cc x).mp hx).1⟩
  obtain ⟨y, hy, z, hz, hxy, hyz, hxz⟩ := comp.2 x' ((cc x).mp hx).2
  exact ⟨y.val, (bc y.val).mpr ⟨y.property, hy⟩, z.val, (ac z.val).mpr ⟨z.property, hz⟩,
    (gq x' y).mpr hxy, (gp y z).mpr hyz, (gr x' z).mpr hxz⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 原关系中的参数所属与完整公式真值

源性质与完整记录共用同一真值解释。该基础层不依赖有限列或历史编码，
故原源接口可以直接使用它；全部声明由原记录模块迁入。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def rr_params_m {d} : {n : Nat} → (Fin n → Term d) → Term d → Formula 1 d
  | 0, _, _ => .truth
  | n+1, v, X => .conj (.mem (v 0) X) (rr_params_m (n := n) (fun i => v i.succ) X)

theorem rr_params_closed_l {d n} (v : Fin n → Term d) (X : Term d)
    (hv : ∀ i, (v i).freeSupport = []) (hX : X.freeSupport = []) : (rr_params_m v X).FreeClosed := by
  induction n with
  | zero => trivial
  | succ n ih => exact ⟨⟨hv 0, hX⟩, ih (fun i => v i.succ) (fun i => hv i.succ)⟩

theorem rr_params_sat_l {d n} (ρ : Env M d) (v : Fin n → Term d) (X : Term d) :
    Formula.satisfies ρ (rr_params_m v X) ↔ ∀ i, M.mem ((v i).eval ρ) (X.eval ρ) := by
  induction n with
  | zero => exact ⟨fun _ i => Fin.elim0 i, fun _ => trivial⟩
  | succ n ih =>
    rw [rr_params_m, Formula.satisfies_conj_iff, ih]
    exact ⟨fun h => Fin.cases h.1 h.2, fun h => ⟨h 0, fun i => h i.succ⟩⟩

def Rr_truth_d {n} (X R : M.Domain) (φ : Formula 1 (n+1)) (v : Fin (n+1) → M.Domain) : Prop :=
  ∃ h : ∀ i, M.mem (v i) X,
    Formula.satisfies (⟨fun i => ⟨v i, h i⟩, fun _ => ⟨v 0, h 0⟩⟩ :
      Env (smdl_structure_l I (R := R) ⟨v 0, h 0⟩) (n+1)) φ

def rr_truth_m {d n} (φ : Formula 1 (n+1)) (X R : Term d) (v : Fin (n+1) → Term d) : Formula 1 d :=
  .conj (rr_params_m v X) (rr_rel_m 𝒞 φ X R v)

theorem rr_truth_closed_l {d n} (φ : Formula 1 (n+1)) (closed : φ.FreeClosed)
    (X R : Term d) (v : Fin (n+1) → Term d) (hX : X.freeSupport = []) (hR : R.freeSupport = [])
    (hv : ∀ i, (v i).freeSupport = []) : (rr_truth_m (𝒞 := 𝒞) φ X R v).FreeClosed :=
  ⟨rr_params_closed_l v X hv hX, rr_rel_closed_l 𝒞 φ closed X R v hX hR hv⟩

theorem rr_truth_sat_l {d n} (ρ : Env M d) (φ : Formula 1 (n+1)) (closed : φ.FreeClosed)
    (X R : Term d) (v : Fin (n+1) → Term d) :
    Formula.satisfies ρ (rr_truth_m (𝒞 := 𝒞) φ X R v) ↔
      Rr_truth_d I (X.eval ρ) (R.eval ρ) φ (fun i => (v i).eval ρ) := by
  rw [rr_truth_m, Formula.satisfies_conj_iff, rr_params_sat_l]
  have read (h : ∀ i, M.mem ((v i).eval ρ) (X.eval ρ)) := rr_rel_sat_l I
    (R := R.eval ρ) ⟨(v 0).eval ρ, h 0⟩ φ closed
    ⟨fun i => ⟨(v i).eval ρ, h i⟩, fun _ => ⟨(v 0).eval ρ, h 0⟩⟩ ρ X R v rfl rfl (fun _ => rfl)
  exact ⟨fun ⟨h, valid⟩ => ⟨h, (read h).mp valid⟩, fun ⟨h, valid⟩ => ⟨h, (read h).mpr valid⟩⟩

/-- 已有对象码的赋值直接解码；不重新选择各坐标。 -/
theorem rr_truth_native_l {X R : M.Domain} (nx : ∃ x, M.mem x X)
    {n} (φ : Formula 1 (n+1)) (closed : φ.FreeClosed)
    (v : Fin (n+1) → (smdl_structure_l I (R := R) nx).Domain) :
    Rr_truth_d I X R φ (fun i => (v i).val) ↔
      Formula.satisfies (⟨v, fun _ => v 0⟩ : Env (smdl_structure_l I (R := R) nx) (n+1)) φ := by
  constructor
  · rintro ⟨hv, valid⟩
    exact (Formula.closed_env_l φ closed (funext fun i => Subtype.ext rfl)).mp valid
  · intro valid
    exact ⟨fun i => (v i).property,
      (Formula.closed_env_l φ closed (funext fun i => Subtype.ext rfl)).mpr valid⟩

theorem Rr_truth_d.map_l (hZF : M.Models ZF) {ω c d X R Y S j : M.Domain}
    (hω : M.IsOmega ω) (mx : Smdl_d I c X R) (my : Smdl_d I d Y S) (map : Smap_d I ω c d X Y j)
    {n} {φ : Formula 1 (n+1)} (closed : φ.FreeClosed) {v w : Fin (n+1) → M.Domain}
    (h : Rr_truth_d I X R φ v) (images : ∀ i, M.PairMember I (v i) (w i) j) : Rr_truth_d I Y S φ w := by
  obtain ⟨hv, valid⟩ := h
  have hw i := map.1.1.output_mem_of_pairMember (images i)
  exact ⟨hw, (smap_source_l I hZF hω mx my map φ closed
    ⟨fun i => ⟨v i, hv i⟩, fun _ => ⟨v 0, hv 0⟩⟩
    ⟨fun i => ⟨w i, hw i⟩, fun _ => ⟨w 0, hw 0⟩⟩ images).mp valid⟩

/-- 沿实际初等图回拉同一参数公式；参数所属由图本身给出。 -/
theorem Rr_truth_d.pull_l (hZF : M.Models ZF) {ω c d X R Y S j : M.Domain}
    (hω : M.IsOmega ω) (mx : Smdl_d I c X R) (my : Smdl_d I d Y S) (map : Smap_d I ω c d X Y j)
    {n} {φ : Formula 1 (n+1)} (closed : φ.FreeClosed) {v w : Fin (n+1) → M.Domain}
    (h : Rr_truth_d I Y S φ w) (images : ∀ i, M.PairMember I (v i) (w i) j) : Rr_truth_d I X R φ v := by
  obtain ⟨hw, valid⟩ := h
  have hv i := map.1.1.input_mem_of_pairMember (images i)
  exact ⟨hv, (smap_source_l I hZF hω mx my map φ closed
    ⟨fun i => ⟨v i, hv i⟩, fun _ => ⟨v 0, hv 0⟩⟩
    ⟨fun i => ⟨w i, hw i⟩, fun _ => ⟨w 0, hw 0⟩⟩ images).mpr valid⟩

theorem rr_truth_mem_l {c X R : M.Domain} (trans : M.TransitiveSet X) (model : Smem_d I c X R)
    {n} (φ : Formula 1 (n+1)) (delta : φ.IsDelta0) (v : Fin (n+1) → M.Domain) :
    Rr_truth_d I X R φ v ↔ (∀ i, M.mem (v i) X) ∧
      Formula.satisfies (⟨v, fun _ => v 0⟩ : Env M (n+1)) φ := by
  have read (hv : ∀ i, M.mem (v i) X) :=
    (smem_formula_l I model ⟨⟨v 0, hv 0⟩⟩ φ
      ⟨fun i => ⟨v i, hv i⟩, fun _ => ⟨v 0, hv 0⟩⟩).symm.trans
      (rt_model_delta_l trans ⟨⟨v 0, hv 0⟩⟩ delta _)
  exact ⟨fun ⟨hv, h⟩ => ⟨hv, (read hv).mp h⟩, fun ⟨hv, h⟩ => ⟨hv, (read hv).mpr h⟩⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 原关系中的内部有限序数最大元

沿已有复制图比较原关系序数。归纳只要求背景内部有限，允许非标准有限集合，
不额外要求原模型满足 KP。最大元保留为给定集合的实际成员。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def rr_ord_m {d} (X R a : Term d) : Formula 1 d :=
  rr_truth_m (𝒞 := kpair_convention_l) (KP.ord0_m .newest) X R (fun _ : Fin 1 => a)

@[simp] theorem rr_ord_closed_l {d} (X R a : Term d)
    (hx : X.freeSupport = []) (hr : R.freeSupport = []) (ha : a.freeSupport = []) :
    (rr_ord_m X R a).FreeClosed :=
  rr_truth_closed_l _ (by simp -implicitDefEqProofs) X R _ hx hr (fun _ => ha)

theorem rr_ord_sat_l (I : kpair_convention_l.Interpretation M) {d}
    (η : Env M d) (X R a : Term d) :
    Formula.satisfies η (rr_ord_m X R a) ↔
      Rr_truth_d I (X.eval η) (R.eval η) (KP.ord0_m .newest) (fun _ : Fin 1 => a.eval η) :=
  rr_truth_sat_l I η _ (by simp -implicitDefEqProofs) X R _

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem rr_finite_max_l {ω c d X R Y S j D : M.Domain} (hω : M.IsOmega ω)
    (mx : Smdl_d I c X R) (my : Smem_d I d Y S) (trans : M.TransitiveSet Y)
    (map : Smap_d I ω c d X Y j)
    (finite : Finite_d I ω D)
    (ord : ∀ x, M.mem x D → Rr_truth_d I X R (KP.ord0_m .newest) (fun _ : Fin 1 => x))
    (nonempty : ∃ x, M.mem x D) :
    ∃ b, M.mem b D ∧ ∀ x, M.mem x D → Rd_entry_d x b R ∨ x = b := by
  let N := smdl_structure_l I (R := R) mx.2.1
  have read x (h : Rr_truth_d I X R (KP.ord0_m .newest) (fun _ : Fin 1 => x)) :
      N.TransitiveSet ⟨x, h.1 0⟩ :=
    ((rr_truth_native_l I mx.2.1 (KP.ord0_m .newest)
      (by simp -implicitDefEqProofs) (fun _ : Fin 1 => ⟨x, h.1 0⟩)).mp h).1
  have cmp a b (ha : Rr_truth_d I X R (KP.ord0_m .newest) (fun _ : Fin 1 => a))
      (hb : Rr_truth_d I X R (KP.ord0_m .newest) (fun _ : Fin 1 => b)) :
      a = b ∨ Rd_entry_d a b R ∨ Rd_entry_d b a R := by
    obtain ⟨a', _, aa⟩ := map.1.1.2.2 a (ha.1 0)
    obtain ⟨b', _, bb⟩ := map.1.1.2.2 b (hb.1 0)
    have ordinal x x' (hx : Rr_truth_d I X R (KP.ord0_m .newest) (fun _ : Fin 1 => x))
        (image : Rd_entry_d x x' j) : M.IsOrdinal x' :=
      (KP.ord0_sat_l (ZF.modelsKP hZF) _ .newest).mp
        (((rr_truth_mem_l I trans my (KP.ord0_m .newest) (KP.ord0_delta_l _)
          (fun _ : Fin 1 => x')).mp (hx.map_l I hZF hω mx my.1 map
            (by simp -implicitDefEqProofs) (fun _ => image))).2)
    rcases (ordinal a a' ha aa).trichotomy hZF.1 (ordinal b b' hb bb)
        (KP.difference_exists_d (ZF.modelsKP hZF)) (KP.intersection_exists_d (ZF.modelsKP hZF) a' b') with eq | lt | gt
    · exact Or.inl (map.1.2 a b b' (hZF.1.eq_of_same_members a' b' eq ▸ aa) bb)
    · exact Or.inr (Or.inl ((map.relation_l I hZF hω mx my.1 aa bb).mpr
        ((my.2 a' b').mpr ⟨map.1.1.output_mem_of_pairMember aa, map.1.1.output_mem_of_pairMember bb, lt⟩)))
    · exact Or.inr (Or.inr ((map.relation_l I hZF hω mx my.1 bb aa).mpr
        ((my.2 b' a').mpr ⟨map.1.1.output_mem_of_pairMember bb, map.1.1.output_mem_of_pairMember aa, gt⟩)))
  let ρ : Env M 2 := ⟨Fin.cases R (fun _ => X), fun _ => X⟩
  let φ : UnarySchema 2 := {
    body := .imp (Formula.forallMem .newest (rr_ord_m (.bound 3) (.bound 2) .newest))
      (.disj (.forallE (.neg (.mem .newest (.bound 1))))
        (.existsE (.conj (.mem .newest (.bound 1))
          (Formula.forallMem (.bound 1) (.disj (rd_entry0_m .newest (.bound 1) (.bound 3))
            (Formula.extensionalEq .newest (.bound 1))))))) }
  have sat A : φ.denote ρ A ↔
      (∀ x, M.mem x A → Rr_truth_d I X R (KP.ord0_m .newest) (fun _ : Fin 1 => x)) →
      (∀ x, ¬ M.mem x A) ∨ ∃ b, M.mem b A ∧ ∀ x, M.mem x A → Rd_entry_d x b R ∨ x = b := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_imp_iff, Formula.satisfies_forallMem_iff,
      rr_ord_sat_l I, Formula.satisfies_disj_iff, Formula.satisfies_forall_iff, Formula.satisfies_neg_iff,
      Formula.satisfies_mem_iff, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      rd_entry0_sat_l hZF.1, Formula.satisfies_extensionalEq_iff_eq hZF.1]; rfl
  have all := ZF.finite_ind_l I hZF hω φ ρ (fun A empty => (sat A).mpr (fun _ => Or.inl empty))
    (fun A a B _ ih insert => (sat B).mpr (fun hb => by
      have ha := (insert a).mpr (Or.inr rfl)
      rcases (sat A).mp ih (fun x hx => hb x ((insert x).mpr (Or.inl hx))) with empty | ⟨b, hba, max⟩
      · exact Or.inr ⟨a, ha, fun x hx => ((insert x).mp hx).elim
          (fun hx => (empty x hx).elim) Or.inr⟩
      · have hbb := (insert b).mpr (Or.inl hba)
        let b₀ : N.Domain := ⟨b, (hb b hbb).1 0⟩
        rcases cmp b a (hb b hbb) (hb a ha) with eq | lt | gt
        · subst b
          exact Or.inr ⟨a, ha, fun x hx => ((insert x).mp hx).elim (max x) Or.inr⟩
        · exact Or.inr ⟨a, ha, fun x hx => ((insert x).mp hx).elim (fun hx =>
            (max x hx).elim (fun hxb => Or.inl (read a (hb a ha) b₀ lt
              ⟨x, (hb x ((insert x).mpr (Or.inl hx))).1 0⟩ hxb))
              (fun eq => Or.inl (eq ▸ lt))) Or.inr⟩
        · exact Or.inr ⟨b, hbb, fun x hx => ((insert x).mp hx).elim (max x)
            (fun eq => Or.inl (eq ▸ gt))⟩)) D finite
  exact ((sat D).mp all ord).elim (fun empty => (nonempty.elim fun x hx => empty x hx).elim) id

end YesMetaZFC.SetTheory.Internal

/-! ## 原关系模型的幂集计数不变量

δ 的幂集对象和成员载体均为实际集合；不变量只保存所需幂集可数性，
不要求整份模型可数。原生读写用于同一次施加前后的状态登记。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def Pc_count_d (I : kpair_convention_l.Interpretation M) (Ω X R δ : M.Domain) : Prop :=
  ∃ P B, Rr_truth_d I (n := 1) X R (Formula.isPowerSet (.bound 0) (.bound 1))
    (Fin.cases P (fun _ => δ)) ∧
    (∀ x, M.mem x B ↔ M.mem x X ∧ Rd_entry_d x P R) ∧ M.CardinalLessOrEqual I B Ω

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Pc_count_d.native_l {Ω X R : M.Domain} (nx : ∃ x, M.mem x X)
    (δ : (smdl_structure_l I (R := R) nx).Domain) (h : Pc_count_d I Ω X R δ.val) :
    ∃ P : (smdl_structure_l I (R := R) nx).Domain, ∃ B,
      (smdl_structure_l I (R := R) nx).IsPowerSetOf P δ ∧
      (∀ x, M.mem x B ↔ M.mem x X ∧ Rd_entry_d x P.val R) ∧ M.CardinalLessOrEqual I B Ω := by
  obtain ⟨P,B,power,carrier,count⟩ := h
  let P' : (smdl_structure_l I (R := R) nx).Domain := ⟨P,power.1 0⟩
  let v : Fin 2 → (smdl_structure_l I (R := R) nx).Domain := Fin.cases P' (fun _ => δ)
  have read := rr_truth_native_l I nx (Formula.isPowerSet (.bound 0) (.bound 1))
    (by simp -implicitDefEqProofs) v
  have values : (fun i => (v i).val) =
      Fin.cases P (fun _ => δ.val) := funext (Fin.cases rfl (fun _ => rfl))
  rw [values] at read
  have truth := read.mp power
  exact ⟨P',B,(Formula.satisfies_isPowerSet_iff ..).mp truth,carrier,count⟩

theorem pc_count_l {Ω X R B : M.Domain} (nx : ∃ x, M.mem x X)
    (δ P : (smdl_structure_l I (R := R) nx).Domain)
    (power : (smdl_structure_l I (R := R) nx).IsPowerSetOf P δ)
    (carrier : ∀ x, M.mem x B ↔ M.mem x X ∧ Rd_entry_d x P.val R)
    (count : M.CardinalLessOrEqual I B Ω) : Pc_count_d I Ω X R δ.val := by
  let v : Fin 2 → (smdl_structure_l I (R := R) nx).Domain := Fin.cases P (fun _ => δ)
  have truth := (rr_truth_native_l I nx (Formula.isPowerSet (.bound 0) (.bound 1))
    (by simp -implicitDefEqProofs) v).mpr
      ((Formula.satisfies_isPowerSet_iff ..).mpr power)
  have values : (fun i => (v i).val) =
      Fin.cases P.val (fun _ => δ.val) := funext (Fin.cases rfl (fun _ => rfl))
  exact ⟨P.val,B,values ▸ truth,carrier,count⟩

theorem Pc_count_d.support_l {Ω X R L : M.Domain} (nx : ∃ x, M.mem x X)
    (native : (smdl_structure_l I (R := R) nx).Models ZF)
    (δ ℓ : (smdl_structure_l I (R := R) nx).Domain)
    (h : Pc_count_d I Ω X R δ.val)
    (ordinal : (smdl_structure_l I (R := R) nx).IsOrdinal δ)
    (below : (smdl_structure_l I (R := R) nx).mem ℓ δ)
    (length : ∀ x, M.mem x L ↔ M.mem x X ∧ Rd_entry_d x ℓ.val R) :
    M.CardinalLessOrEqual I L Ω := by
  obtain ⟨P,B,power,carrier,count⟩ := h.native_l hZF nx δ
  exact rr_power_ordinal_count_l hZF nx native δ ℓ P ordinal below power carrier count length

end YesMetaZFC.SetTheory.Internal

/-! ## 实际幂集计数的一阶表示 -/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def pc_count_m {d} (Ω X R δ : Term d) : Formula 1 d := set[d] ⟪∃ P B,
  ⌜fun X R P δ => rr_truth_m (𝒞 := kpair_convention_l)
    (Formula.isPowerSet (.bound 0) (.bound 1)) X R (Fin.cases P (fun _ : Fin 1 => δ))⌝ₚ
      (⌜X⌝ₛ,⌜R⌝ₛ,P,⌜δ⌝ₛ) ∧
  (∀ x, x ∈ B ↔ x ∈ ⌜X⌝ₛ ∧ ⌜rd_entry0_m⌝ₚ(x,P,⌜R⌝ₛ)) ∧
  ⌜Formula.cardinalLessOrEqual kpair_convention_l⌝ₚ(B,⌜Ω⌝ₛ)⟫

@[simp] theorem pc_count_closed_l {d} (Ω X R δ : Term d)
    (hw : Ω.freeSupport = []) (hx : X.freeSupport = []) (hr : R.freeSupport = [])
    (hd : δ.freeSupport = []) : (pc_count_m Ω X R δ).FreeClosed := by
  simp -implicitDefEqProofs [pc_count_m,Definitional.Formula.FreeClosed,hw,hx,hr]
  apply rr_truth_closed_l _ (by simp -implicitDefEqProofs) <;>
    simp [hx,hr,hd,Fin.forall_fin_succ]

theorem pc_count_sat_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M)
    {d} (ρ : Env M d) (Ω X R δ : Term d) : Formula.satisfies ρ (pc_count_m Ω X R δ) ↔
      Pc_count_d I (Ω.eval ρ) (X.eval ρ) (R.eval ρ) (δ.eval ρ) := by
  have eval {n} (ρ : Env M n) (A B : Term n) :
      (fun i : Fin 2 => ((Fin.cases A (fun _ : Fin 1 => B) : Fin 2 → Term n) i).eval ρ) =
        Fin.cases (A.eval ρ) (fun _ => B.eval ρ) := funext (Fin.cases rfl (fun _ => rfl))
  simp only [pc_count_m,Pc_count_d,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
    rr_truth_sat_l I _ (Formula.isPowerSet (.bound 0) (.bound 1)) (by simp -implicitDefEqProofs),eval,
    Formula.satisfies_forall_iff,
    Formula.satisfies_iff_iff,Formula.satisfies_mem_iff,rd_entry0_sat_l hE,
    Formula.satisfies_cardinalLessOrEqual_iff I hE,Definitional.Term.eval_weaken]
  rfl

end YesMetaZFC.SetTheory.Internal

/-! ## 任意关系模型中的内部统一见证程序

原公式可以有非标准内部长度；这里只追加固定的函数图模板和量词。
函数对象、定义域及值域均按原关系解释，不要求整个模型坍塌。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M) (hZF : M.Models ZF)
include hZF

theorem sfm_total_raw_l {ω n F r i j s} (hω : M.IsOmega ω)
    (hF : Sfm_d I ω n F) (hr : M.mem r n) (hi : M.mem i ω) (hj : M.mem j ω)
    (hs : M.mem s ω) (hsi : s ≠ i) : ∃ m G k, Sbuild_d I ω n F m G k ∧ ∀ X R E c f
      (model : Smdl_d I c X R) (D : (smdl_structure_l I (R := R) model.2.1).Domain),
      M.IsFunctionSpace I E ω X → M.mem f E → M.PairMember I s D.val f →
      (Ssat_d I X R E G m k f ↔ ∀ x : (smdl_structure_l I (R := R) model.2.1).Domain,
        M.PairMember I x.val D.val R → ∃ y : (smdl_structure_l I (R := R) model.2.1).Domain,
          Sbin_d I X R E F n r i j f x.val y.val) := by
  obtain ⟨n₁, F₁, r₁, h₁, a₁⟩ := sfm_ex_l I hZF hω hF hj hr
  obtain ⟨n₂, F₂, h₂, a₂⟩ := sfm_rel_l I hZF hω h₁.program hi hs
  obtain ⟨n₃, F₃, r₃, h₃, a₃⟩ := sfm_imp_l I hZF hω h₂.program h₂.root (h₂.span r₁ h₁.root)
  obtain ⟨m, G, k, h₄, a₄⟩ := sfm_all_l I hZF hω h₃.program hi h₃.root
  refine ⟨m, G, k, ((h₁.comp I h₂).comp I h₃).comp I h₄, fun X R E c f model D hE hf hD => ?_⟩
  have read x g (hx : M.mem x X) (hu : Senv_update_d I f i x g) :
      Ssat_d I X R E F₃ n₃ r₃ g ↔ (M.PairMember I x D.val R →
        ∃ y, M.mem y X ∧ Sbin_d I X R E F n r i j f x y) := by
    have hg := (hE g).mpr (hu.function_l I ((hE f).mp hf) hi hx)
    rw [a₃ X R E g hg, a₂ X R E g x D.val hE hg ((hu.2 i x).mpr (Or.inl ⟨rfl, rfl⟩))
      ((hu.2 s D.val).mpr (Or.inr ⟨hsi, hD⟩)), ← h₂.sat_l I hZF h₁.program h₁.root X R E g, a₁ X R E g hg]
    exact imp_congr Iff.rfl (exists_congr fun y =>
      ⟨fun ⟨v, hy, hv, ht⟩ => ⟨hy, (sbin_update_l I hZF.1 hu).mpr ⟨v, hv, ht⟩⟩,
        fun ⟨hy, ht⟩ => ((sbin_update_l I hZF.1 hu).mp ht).elim fun v hv => ⟨v, hy, hv⟩⟩)
  rw [a₄ X R E f hE hf]
  constructor
  · intro h x hx
    obtain ⟨g, hg, _⟩ := senv_update_exists_l I hZF ((hE f).mp hf) hi x.property
    obtain ⟨y, hy, hxy⟩ := (read x.val g x.property hg).mp (h x.val g x.property hg) hx
    exact ⟨⟨y, hy⟩, hxy⟩
  · intro h x g hx hg
    exact (read x g hx hg).mpr fun hd => (h ⟨x, hx⟩ hd).elim fun y hy => ⟨y.val, y.property, hy⟩

theorem sfm_function_raw_l {ω n F i s u σ} (hω : M.IsOmega ω)
    (hF : Sfm_d I ω n F) (hσ : M.mem σ ω) (hi : M.mem i σ) (hs : M.mem s σ) (hu : M.mem u σ)
    (hus : u ≠ s) (hui : u ≠ i) : ∃ m G k, Sbuild_d I ω n F m G k ∧ ∀ X R E c f
      (model : Smdl_d I c X R) (B D : (smdl_structure_l I (R := R) model.2.1).Domain),
      Extensional (smdl_structure_l I (R := R) model.2.1) →
      M.IsFunctionSpace I E ω X → M.mem f E → M.PairMember I i B.val f → M.PairMember I s D.val f →
      (Ssat_d I X R E G m k f ↔ ∃ C : (smdl_structure_l I (R := R) model.2.1).Domain, Fn0_d D C B) := by
  let q : Fin 3 → M.Domain := Fin.cases s (Fin.cases u (fun _ => i))
  let φ : Formula 1 3 := fn0_m (.bound 0) (.bound 1) (.bound 2)
  obtain ⟨v, J, r, h, template⟩ := sfm_template_l I hZF hω hF φ (by simp -implicitDefEqProofs [φ])
    q hσ (Fin.cases hs (Fin.cases hu (fun _ => hi)))
  have huω := hω.transitive (ZF.modelsKP hZF) σ hσ u hu
  obtain ⟨m, G, k, g, quantifier⟩ := sfm_ex_l I hZF hω h.program huω h.root
  refine ⟨m, G, k, h.comp I g, fun X R E c f model B D ext hE hf hiB hsD => ?_⟩
  have read (C : (smdl_structure_l I (R := R) model.2.1).Domain) a (ha : Senv_update_d I f u C.val a) :
      Ssat_d I X R E J v r a ↔ Fn0_d D C B := by
    let ρ : Env (smdl_structure_l I (R := R) model.2.1) 3 := ⟨Fin.cases D (Fin.cases C (fun _ => B)), fun _ => B⟩
    exact (template X R model.2.1 E hE a ((hE a).mpr (ha.function_l I ((hE f).mp hf) huω C.property))
      ρ
      (Fin.cases ((ha.2 s D.val).mpr (Or.inr ⟨Ne.symm hus, hsD⟩))
        (Fin.cases ((ha.2 u C.val).mpr (Or.inl ⟨rfl, rfl⟩))
          (fun _ => (ha.2 i B.val).mpr (Or.inr ⟨Ne.symm hui, hiB⟩))))).trans
      (fn0_sat_l ext ρ .newest (.bound 1) (.bound 2))
  rw [quantifier X R E f hf]
  constructor
  · rintro ⟨C, a, hC, ha, ht⟩
    exact ⟨⟨C, hC⟩, (read ⟨C, hC⟩ a ha).mp ht⟩
  · rintro ⟨C, ht⟩
    obtain ⟨a, ha, _⟩ := senv_update_exists_l I hZF ((hE f).mp hf) huω C.property
    exact ⟨C.val, a, C.property, ha, (read C a ha).mpr ht⟩

/-- 对内部原程序统一取值，输出的是原关系模型拥有的函数对象。 -/
theorem sfm_uniform_raw_l {ω n F r i j s t u σ b} (hω : M.IsOmega ω)
    (hF : Sfm_d I ω n F) (hr : M.mem r n) (hσ : M.mem σ ω)
    (hi : M.mem i σ) (hj : M.mem j σ) (hs : M.mem s σ) (ht : M.mem t σ) (hu : M.mem u σ)
    (hij : i ≠ j) (hsi : s ≠ i) (hti : t ≠ i) (htj : t ≠ j) (hst : s ≠ t) (hus : u ≠ s) (hut : u ≠ t)
    (hb : Sbound_d I F b) (htb : ¬ M.mem t b) : ∃ m G k, Sbuild_d I ω n F m G k ∧ ∀ X R E c f
      (model : Smdl_d I c X R) (D : (smdl_structure_l I (R := R) model.2.1).Domain),
      Extensional (smdl_structure_l I (R := R) model.2.1) →
      M.IsFunctionSpace I E ω X → M.mem f E → M.PairMember I s D.val f →
      (Ssat_d I X R E G m k f ↔ ∃ B C : (smdl_structure_l I (R := R) model.2.1).Domain,
        Fn0_d D C B ∧ ∀ x y : (smdl_structure_l I (R := R) model.2.1).Domain,
          Rd_entry_d x y B → Sbin_d I X R E F n r i j f x.val y.val) := by
  have into a (ha : M.mem a σ) := hω.transitive (ZF.modelsKP hZF) σ hσ a ha
  -- s 保存定义域，t 保存待选函数，u 保存其值域；i、j 仍是原公式变量。
  let p : Fin 3 → M.Domain := Fin.cases i (Fin.cases j (fun _ => t))
  let φ : Formula 1 3 := rd_entry0_m (.bound 0) (.bound 1) (.bound 2)
  obtain ⟨n₁, F₁, r₁, h₁, a₁⟩ := sfm_template_l I hZF hω hF φ (by simp -implicitDefEqProofs [φ])
    p hσ (Fin.cases hi (Fin.cases hj (fun _ => ht)))
  obtain ⟨n₂, F₂, r₂, h₂, a₂⟩ := sfm_and_l I hZF hω h₁.program h₁.root (h₁.span r hr)
  obtain ⟨n₃, F₃, r₃, h₃, a₃⟩ := sfm_total_raw_l I hZF hω h₂.program h₂.root (into i hi) (into j hj) (into s hs) hsi
  obtain ⟨n₅, F₅, r₅, h₅, a₅⟩ := sfm_function_raw_l I hZF hω h₃.program hσ ht hs hu hus hut
  obtain ⟨n₆, F₆, r₆, h₆, a₆⟩ := sfm_and_l I hZF hω h₅.program (h₅.span r₃ h₃.root) h₅.root
  obtain ⟨m, G, k, h₇, a₇⟩ := sfm_ex_l I hZF hω h₆.program (into t ht) h₆.root
  refine ⟨m, G, k, ((((h₁.comp I h₂).comp I h₃).comp I h₅).comp I h₆).comp I h₇,
    fun X R E c f model D ext hE hf hD => ?_⟩
  let N := smdl_structure_l I (R := R) model.2.1
  have en := ext
  have body (B : N.Domain) g (hg : Senv_update_d I f t B.val g) :
      Ssat_d I X R E F₆ n₆ r₆ g ↔ ∃ C : N.Domain, Fn0_d D C B ∧
        ∀ x y : N.Domain, Rd_entry_d x y B → Sbin_d I X R E F n r i j f x.val y.val := by
    have hgE := (hE g).mpr (hg.function_l I ((hE f).mp hf) (into t ht) B.property)
    have hsD := (hg.2 s D.val).mpr (Or.inr ⟨hst, hD⟩)
    have htB := (hg.2 t B.val).mpr (Or.inl ⟨rfl, rfl⟩)
    have point (x y : N.Domain) : Sbin_d I X R E F₂ n₂ r₂ i j g x.val y.val ↔
        Rd_entry_d x y B ∧ Sbin_d I X R E F n r i j f x.val y.val := by
      obtain ⟨v, hv, hvf⟩ := senv_update_exists_l I hZF ((hE g).mp hgE) (into i hi) x.property
      obtain ⟨w, hw, hwf⟩ := senv_update_exists_l I hZF hvf (into j hj) y.property
      let ρ : Env N 3 := ⟨Fin.cases x (Fin.cases y (fun _ => B)), fun _ => B⟩
      have hp : ∀ z, M.PairMember I (p z) (ρ.bound z).val w := Fin.cases
        ((hw.2 i x.val).mpr (Or.inr ⟨hij, (hv.2 i x.val).mpr (Or.inl ⟨rfl, rfl⟩)⟩))
        (Fin.cases ((hw.2 j y.val).mpr (Or.inl ⟨rfl, rfl⟩)) (fun _ => (hw.2 t B.val).mpr
          (Or.inr ⟨htj, (hv.2 t B.val).mpr (Or.inr ⟨hti, htB⟩)⟩)))
      have atom := (a₁ X R model.2.1 E hE w ((hE w).mpr hwf) ρ hp).trans
        (rd_entry0_sat_l en ρ .newest (.bound 1) (.bound 2))
      have val : Sbin_d I X R E F n r i j f x.val y.val ↔ Ssat_d I X R E F n r w :=
        (sbin_agree_l I hZF hF hb hr (into i hi) (into j hj) hE hf hgE
        (hg.agree_l I htb) x.property y.property).trans (sbin_value_l I hZF.1 hv hw)
      apply (sbin_value_l I hZF.1 hv hw).trans
      rw [a₂ X R E w ((hE w).mpr hwf), ← h₁.sat_l I hZF hF hr X R E w]
      exact and_congr atom val.symm
    rw [a₆ X R E g hgE, ← h₅.sat_l I hZF h₃.program h₃.root X R E g,
      a₃ X R E c g model D hE hgE hsD, a₅ X R E c g model B D ext hE hgE htB hsD]
    constructor
    · rintro ⟨total, C, fn⟩
      refine ⟨C, fn, fun x y hxy => ?_⟩
      obtain ⟨z, hz⟩ := total x (fn.bound_l hxy).1
      obtain ⟨hxz, truth⟩ := (point x z).mp hz
      have eq := fn.2.2 x (fn.bound_l hxy).1 z (fn.bound_l hxz).2 y (fn.bound_l hxy).2 hxz hxy
      exact congrArg Subtype.val eq ▸ truth
    · rintro ⟨C, fn, truth⟩
      refine ⟨fun x hx => ?_, C, fn⟩
      obtain ⟨y, _, hxy⟩ := fn.2.1 x hx
      exact ⟨y, (point x y).mpr ⟨hxy, truth x y hxy⟩⟩
  rw [a₇ X R E f hf]
  constructor
  · rintro ⟨B, g, hB, hg, h⟩
    obtain ⟨C, fn, truth⟩ := (body ⟨B, hB⟩ g hg).mp h
    exact ⟨⟨B, hB⟩, C, fn, truth⟩
  · rintro ⟨B, C, fn, truth⟩
    obtain ⟨g, hg, _⟩ := senv_update_exists_l I hZF ((hE f).mp hf) (into t ht) B.property
    exact ⟨B.val, g, B.property, hg, (body B g hg).mpr ⟨C, fn, truth⟩⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 原关系模型的普通收集程序

集合界按原成员关系读取。追加的集合变量位于旧程序支撑外，原公式的所有
内部赋值保持不变；这给完整内部 ZFC 的后继传输提供真正的模式程序。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M) (hZF : M.Models ZF)
include hZF

theorem sfm_collect_raw_l {ω n F r i j s t b} (hω : M.IsOmega ω)
    (hF : Sfm_d I ω n F) (hr : M.mem r n) (hi : M.mem i ω) (hj : M.mem j ω)
    (hs : M.mem s ω) (ht : M.mem t ω) (hsi : s ≠ i) (hti : t ≠ i) (htj : t ≠ j) (hst : s ≠ t)
    (hb : Sbound_d I F b) (htb : ¬ M.mem t b) : ∃ m G k, Sbuild_d I ω n F m G k ∧ ∀ X R E c f
      (model : Smdl_d I c X R) (D : (smdl_structure_l I (R := R) model.2.1).Domain),
      M.IsFunctionSpace I E ω X → M.mem f E → M.PairMember I s D.val f →
      (Ssat_d I X R E G m k f ↔ ∃ C : (smdl_structure_l I (R := R) model.2.1).Domain,
        ∀ x : (smdl_structure_l I (R := R) model.2.1).Domain, M.PairMember I x.val D.val R →
          ∃ y : (smdl_structure_l I (R := R) model.2.1).Domain,
            M.PairMember I y.val C.val R ∧ Sbin_d I X R E F n r i j f x.val y.val) := by
  obtain ⟨n₁, F₁, h₁, a₁⟩ := sfm_rel_l I hZF hω hF hj ht
  obtain ⟨n₂, F₂, r₂, h₂, a₂⟩ := sfm_and_l I hZF hω h₁.program h₁.root (h₁.span r hr)
  obtain ⟨n₃, F₃, r₃, h₃, a₃⟩ := sfm_total_raw_l I hZF hω h₂.program h₂.root hi hj hs hsi
  obtain ⟨m, G, k, h₄, a₄⟩ := sfm_ex_l I hZF hω h₃.program ht h₃.root
  refine ⟨m, G, k, ((h₁.comp I h₂).comp I h₃).comp I h₄, fun X R E c f model D hE hf hD => ?_⟩
  have body (C : (smdl_structure_l I (R := R) model.2.1).Domain) g (ug : Senv_update_d I f t C.val g) :
      Ssat_d I X R E F₃ n₃ r₃ g ↔ ∀ x : (smdl_structure_l I (R := R) model.2.1).Domain,
        M.PairMember I x.val D.val R → ∃ y : (smdl_structure_l I (R := R) model.2.1).Domain,
          M.PairMember I y.val C.val R ∧ Sbin_d I X R E F n r i j f x.val y.val := by
    have hg := (hE g).mpr (ug.function_l I ((hE f).mp hf) ht C.property)
    have point (x y : (smdl_structure_l I (R := R) model.2.1).Domain) :
        Sbin_d I X R E F₂ n₂ r₂ i j g x.val y.val ↔
          M.PairMember I y.val C.val R ∧ Sbin_d I X R E F n r i j f x.val y.val := by
      obtain ⟨u, uv, fu⟩ := senv_update_exists_l I hZF ((hE g).mp hg) hi x.property
      obtain ⟨v, vv, fv⟩ := senv_update_exists_l I hZF fu hj y.property
      have htC := (vv.2 t C.val).mpr (Or.inr ⟨htj, (uv.2 t C.val).mpr
        (Or.inr ⟨hti, (ug.2 t C.val).mpr (Or.inl ⟨rfl, rfl⟩)⟩)⟩)
      have val : Sbin_d I X R E F n r i j f x.val y.val ↔ Ssat_d I X R E F n r v :=
        (sbin_agree_l I hZF hF hb hr hi hj hE hf hg (ug.agree_l I htb) x.property y.property).trans
          (sbin_value_l I hZF.1 uv vv)
      apply (sbin_value_l I hZF.1 uv vv).trans
      rw [a₂ X R E v ((hE v).mpr fv), a₁ X R E v y.val C.val hE ((hE v).mpr fv)
        ((vv.2 j y.val).mpr (Or.inl ⟨rfl, rfl⟩)) htC, ← h₁.sat_l I hZF hF hr X R E v]
      exact and_congr Iff.rfl val.symm
    rw [a₃ X R E c g model D hE hg ((ug.2 s D.val).mpr (Or.inr ⟨hst, hD⟩))]
    exact forall_congr' fun x => imp_congr_right fun _ => exists_congr fun y => point x y
  rw [a₄ X R E f hf]
  constructor
  · rintro ⟨C, g, hc, ug, truth⟩
    exact ⟨⟨C, hc⟩, (body ⟨C, hc⟩ g ug).mp truth⟩
  · rintro ⟨C, truth⟩
    obtain ⟨g, ug, _⟩ := senv_update_exists_l I hZF ((hE f).mp hf) ht C.property
    exact ⟨C.val, g, C.property, ug, (body C g ug).mpr truth⟩

end YesMetaZFC.SetTheory.Internal
