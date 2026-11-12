import YesMetaZFC.Model.SetTheory.Relations.Parity
import YesMetaZFC.Model.SetTheory.Source.OmegaClosed
import YesMetaZFC.Model.SetTheory.Reflection.ZfcTransfer

/-! # 原模型切片与实际关系码的语义一致性

切片成员的双重子类型逐项映到同一个背景对象码；该映射满射且完全反映
隶属关系，因此全部原公式保持。这里不假定切片载体在背景中传递。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem rr_cut_formula_l {N R Γ S : M.Domain} (nx : ∃ x, M.mem x N)
    (U : (smdl_structure_l I (R := R) nx).Domain)
    (nu : Nonempty {x : (smdl_structure_l I (R := R) nx).Domain // (smdl_structure_l I (R := R) nx).mem x U})
    (ny : ∃ x, M.mem x Γ)
    (carrier : ∀ x, M.mem x Γ ↔ M.mem x N ∧ M.PairMember I x U.val R)
    (relation : ∀ x y, M.PairMember I x y S ↔ M.mem x Γ ∧ M.mem y Γ ∧ M.PairMember I x y R)
    {n} (φ : Formula 1 n) (ρ : Env (rt_model_l U nu) n) :
    Formula.satisfies ρ φ ↔ Formula.satisfies
      (image_env_l (M := rt_model_l U nu) (N := smdl_structure_l I (R := S) ny)
        (fun x : (rt_model_l U nu).Domain =>
        (⟨x.val.val, (carrier x.val.val).mpr ⟨x.val.property, x.property⟩⟩ :
          (smdl_structure_l I (R := S) ny).Domain)) ρ) φ := by
  let e : (rt_model_l U nu).Domain → (smdl_structure_l I (R := S) ny).Domain :=
    fun x => ⟨x.val.val, (carrier x.val.val).mpr ⟨x.val.property, x.property⟩⟩
  have onto : Function.Surjective e := fun y =>
    ⟨⟨⟨y.val, ((carrier y.val).mp y.property).1⟩, ((carrier y.val).mp y.property).2⟩, rfl⟩
  have atoms x y : (rt_model_l U nu).mem x y ↔ (smdl_structure_l I (R := S) ny).mem (e x) (e y) :=
    ⟨fun h => (relation x.val.val y.val.val).mpr ⟨(e x).property, (e y).property, h⟩,
      fun h => ((relation x.val.val y.val.val).mp h).2.2⟩
  exact formula_image_l e onto atoms φ ρ

/-- 切片原理论沿同一逐项解码保持；这不把外部逐句满足升级成内部模式。 -/
theorem rr_cut_models_l {N R Γ S : M.Domain} (nx : ∃ x, M.mem x N)
    (U : (smdl_structure_l I (R := R) nx).Domain)
    (nu : Nonempty {x : (smdl_structure_l I (R := R) nx).Domain // (smdl_structure_l I (R := R) nx).mem x U})
    (ny : ∃ x, M.mem x Γ)
    (carrier : ∀ x, M.mem x Γ ↔ M.mem x N ∧ M.PairMember I x U.val R)
    (relation : ∀ x y, M.PairMember I x y S ↔ M.mem x Γ ∧ M.mem y Γ ∧ M.PairMember I x y R)
    (T : Theory) (source : (rt_model_l U nu).Models T) :
    (smdl_structure_l I (R := S) ny).Models T := by
  refine ⟨⟨fun x y same => ?_⟩, fun s hs => ?_⟩
  · let x' : (rt_model_l U nu).Domain := ⟨⟨x.val, ((carrier x.val).mp x.property).1⟩,
      ((carrier x.val).mp x.property).2⟩
    let y' : (rt_model_l U nu).Domain := ⟨⟨y.val, ((carrier y.val).mp y.property).1⟩,
      ((carrier y.val).mp y.property).2⟩
    have eq : x' = y' := source.1.eq_of_same_members x' y' (fun z => by
      have hz := (carrier z.val.val).mpr ⟨z.val.property, z.property⟩
      have rel (a : (smdl_structure_l I (R := S) ny).Domain) :
          M.PairMember I z.val.val a.val S ↔ M.PairMember I z.val.val a.val R :=
        (relation z.val.val a.val).trans ((and_iff_right hz).trans (and_iff_right a.property))
      exact (rel x).symm.trans ((same ⟨z.val.val, hz⟩).trans (rel y)))
    exact Subtype.ext (congrArg (fun z : (rt_model_l U nu).Domain => z.val.val) eq)
  · rw [Structure.satisfiesSentence_iff]
    intro f
    have inhabited := nu
    obtain ⟨v⟩ := inhabited
    let ρ : Env (rt_model_l U nu) 0 := ⟨Fin.elim0, fun _ => v⟩
    have valid := (Structure.satisfiesSentence_iff ..).mp (source.2 s hs) ρ.free
    have moved := (rr_cut_formula_l I nx U nu ny carrier relation s.formula ρ).mp valid
    exact (Formula.closed_env_l s.formula s.freeClosed (funext fun i => Fin.elim0 i)).mp moved

end YesMetaZFC.SetTheory.Internal

/-! ## 两个原关系模型之间的完整切片解释

源切片的传递性在源模型内部解释。实际坐标图的全部前驱方程给出有界
公式的双向保持，不把源对象码的背景隶属关系当成源模型隶属关系。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

/-- 以图中的实际点对为共同结构，两侧投影直接保持全部有界公式。 -/
theorem rr_graph_delta_l {N R Γ C W t : M.Domain} (nx : ∃ x, M.mem x N) (ny : ∃ y, M.mem y C)
    (ng : ∃ x, M.mem x Γ) (inside : M.MemberSubset Γ N)
    (down : ∀ x y, M.mem x Γ → M.mem y N → M.PairMember I y x R → M.mem y Γ)
    (ft : M.IsSetInjectionFromTo I t Γ C)
    (pred : ∀ x E, M.PairMember I x E t → ∀ P,
      M.PairMember I P E W ↔ ∃ y, M.PairMember I y x R ∧ M.PairMember I y P t)
    {n} (φ : Formula 1 n) (closed : φ.FreeClosed) (delta : φ.IsDelta0)
    (ρ : Env (smdl_structure_l I (R := R) nx) n) (η : Env (smdl_structure_l I (R := W) ny) n)
    (params : ∀ i, M.PairMember I (ρ.bound i).val (η.bound i).val t) :
    Formula.satisfies ρ φ ↔ Formula.satisfies η φ := by
  obtain ⟨x, hx⟩ := ng
  obtain ⟨y, _, hxy⟩ := ft.1.2.2 x hx
  let A : Structure := {
    Domain := {p : M.Domain × M.Domain // M.PairMember I p.1 p.2 t}
    nonempty := ⟨⟨(x, y), hxy⟩⟩
    mem a b := M.PairMember I a.val.1 b.val.1 R }
  let f : A.Domain → (smdl_structure_l I (R := R) nx).Domain :=
    fun a => ⟨a.val.1, inside _ (ft.1.input_mem_of_pairMember a.property)⟩
  let g : A.Domain → (smdl_structure_l I (R := W) ny).Domain :=
    fun a => ⟨a.val.2, ft.1.output_mem_of_pairMember a.property⟩
  have injf : Function.Injective f := by
    intro a b eq
    have first : a.val.1 = b.val.1 := congrArg Subtype.val eq
    exact Subtype.ext (Prod.ext first (ft.1.1.2 b.val.1 a.val.2 b.val.2 (first ▸ a.property) b.property))
  have injg : Function.Injective g := by
    intro a b eq
    have last : a.val.2 = b.val.2 := congrArg Subtype.val eq
    exact Subtype.ext (Prod.ext (ft.2 a.val.1 b.val.1 b.val.2 (last ▸ a.property) b.property) last)
  have left a (v : (smdl_structure_l I (R := R) nx).Domain) :
      (smdl_structure_l I (R := R) nx).mem v (f a) ↔ ∃ b, A.mem b a ∧ f b = v := by
    constructor
    · intro h
      obtain ⟨w, _, hvw⟩ := ft.1.2.2 v.val
        (down a.val.1 v.val (ft.1.input_mem_of_pairMember a.property) v.property h)
      exact ⟨⟨(v.val, w), hvw⟩, h, Subtype.ext rfl⟩
    · rintro ⟨b, h, eq⟩
      change M.PairMember I v.val a.val.1 R
      exact (show b.val.1 = v.val from congrArg Subtype.val eq) ▸ h
  have right a (v : (smdl_structure_l I (R := W) ny).Domain) :
      (smdl_structure_l I (R := W) ny).mem v (g a) ↔ ∃ b, A.mem b a ∧ g b = v := by
    apply (pred a.val.1 a.val.2 a.property v.val).trans
    exact ⟨fun ⟨w, hw, hwv⟩ => ⟨⟨(w, v.val), hwv⟩, hw, Subtype.ext rfl⟩,
      fun ⟨b, hb, eq⟩ => ⟨b.val.1, hb, (show b.val.2 = v.val from congrArg Subtype.val eq) ▸ b.property⟩⟩
  let θ : Env A n := ⟨fun i => ⟨((ρ.bound i).val, (η.bound i).val), params i⟩, fun _ => ⟨(x, y), hxy⟩⟩
  have source := Formula.closed_env_l φ closed (show (image_env_l f θ).bound = ρ.bound from rfl)
  have target := Formula.closed_env_l φ closed (show (image_env_l g θ).bound = η.bound from rfl)
  exact source.symm.trans ((delta0_image_l f injf left delta θ).symm.trans
    ((delta0_image_l g injg right delta θ).trans target))

theorem rr_native_delta_l {N R Γ C W t : M.Domain} (nx : ∃ x, M.mem x N) (ny : ∃ y, M.mem y C)
    (U : (smdl_structure_l I (R := R) nx).Domain)
    (trans : (smdl_structure_l I (R := R) nx).TransitiveSet U)
    (nu : Nonempty {x : (smdl_structure_l I (R := R) nx).Domain // (smdl_structure_l I (R := R) nx).mem x U})
    (carrier : ∀ x, M.mem x Γ ↔ M.mem x N ∧ M.PairMember I x U.val R)
    (ft : M.IsSetInjectionFromTo I t Γ C)
    (pred : ∀ x E, M.PairMember I x E t → ∀ P,
      M.PairMember I P E W ↔ ∃ y, M.PairMember I y x R ∧ M.PairMember I y P t)
    {n} (φ : Formula 1 n) (closed : φ.FreeClosed) (delta : φ.IsDelta0)
    (ρ : Env (rt_model_l U nu) n) (η : Env (smdl_structure_l I (R := W) ny) n)
    (params : ∀ i, M.PairMember I (ρ.bound i).val.val (η.bound i).val t) :
    Formula.satisfies (image_env_l Subtype.val ρ) φ ↔ Formula.satisfies η φ := by
  have ng : ∃ x, M.mem x Γ := nu.elim fun x => ⟨x.val.val, (carrier x.val.val).mpr ⟨x.val.property, x.property⟩⟩
  let incl : (rt_model_l U nu).Domain → (smdl_structure_l I (R := R) nx).Domain := Subtype.val
  exact rr_graph_delta_l I nx ny ng (fun x hx => ((carrier x).mp hx).1)
    (fun x y hx hy hyx => (carrier y).mpr ⟨hy,
      trans ⟨x, ((carrier x).mp hx).1⟩ ((carrier x).mp hx).2 ⟨y, hy⟩ hyx⟩)
    ft pred φ closed delta (image_env_l incl ρ) η params


/-- 同一原函数码的函数性与求值均由完整前驱图读取。 -/
theorem rr_native_function_l {N R Γ C W k : M.Domain} (nx : ∃ x, M.mem x N) (ny : ∃ y, M.mem y C)
    (en : Extensional (smdl_structure_l I (R := R) nx)) (ec : Extensional (smdl_structure_l I (R := W) ny))
    (U : (smdl_structure_l I (R := R) nx).Domain)
    (trans : (smdl_structure_l I (R := R) nx).TransitiveSet U)
    (carrier : ∀ x, M.mem x Γ ↔ M.mem x N ∧ M.PairMember I x U.val R)
    (fk : M.IsSetInjectionFromTo I k Γ C)
    (pred : ∀ x E, M.PairMember I x E k → ∀ P,
      M.PairMember I P E W ↔ ∃ y, M.PairMember I y x R ∧ M.PairMember I y P k)
    (d a f : (smdl_structure_l I (R := R) nx).Domain)
    (d' a' f' : (smdl_structure_l I (R := W) ny).Domain)
    (hd : M.PairMember I d.val d'.val k) (ha : M.PairMember I a.val a'.val k)
    (hf : M.PairMember I f.val f'.val k) (fn : Fn0_d d a f) :
    Fn0_d d' a' f' ∧ ∀ x y : (smdl_structure_l I (R := R) nx).Domain,
      ∀ x' y' : (smdl_structure_l I (R := W) ny).Domain,
        M.PairMember I x.val x'.val k → M.PairMember I y.val y'.val k →
          (Rd_entry_d x y f ↔ Rd_entry_d x' y' f') := by
  let N₀ := smdl_structure_l I (R := R) nx
  let C₀ := smdl_structure_l I (R := W) ny
  have member (x : N₀.Domain) (y : C₀.Domain) (h : M.PairMember I x.val y.val k) : N₀.mem x U :=
    ((carrier x.val).mp (fk.1.input_mem_of_pairMember h)).2
  let nu : Nonempty {x : N₀.Domain // N₀.mem x U} := ⟨⟨d, member d d' hd⟩⟩
  let ρ : Env (rt_model_l U nu) 3 := ⟨Fin.cases ⟨f, member f f' hf⟩
    (Fin.cases ⟨a, member a a' ha⟩ (fun _ => ⟨d, member d d' hd⟩)), fun _ => ⟨d, member d d' hd⟩⟩
  let η : Env C₀ 3 := ⟨Fin.cases f' (Fin.cases a' (fun _ => d')), fun _ => d'⟩
  have moved := rr_native_delta_l I nx ny U trans nu carrier fk pred (fn0_m (.bound 2) (.bound 1) .newest)
    (by simp -implicitDefEqProofs) (fn0_delta_l ..) ρ η (Fin.cases hf (Fin.cases ha (fun _ => hd)))
  refine ⟨(fn0_sat_l ec ..).mp (moved.mp ((fn0_sat_l en ..).mpr fn)), fun x y x' y' hx hy => ?_⟩
  let σ : Env (rt_model_l U nu) 3 := ⟨Fin.cases ⟨f, member f f' hf⟩
    (Fin.cases ⟨y, member y y' hy⟩ (fun _ => ⟨x, member x x' hx⟩)), fun _ => ⟨d, member d d' hd⟩⟩
  let τ : Env C₀ 3 := ⟨Fin.cases f' (Fin.cases y' (fun _ => x')), fun _ => d'⟩
  exact (rd_entry0_sat_l en ..).symm.trans
    ((rr_native_delta_l I nx ny U trans nu carrier fk pred (rd_entry0_m (.bound 2) (.bound 1) .newest)
      (by simp -implicitDefEqProofs) (rd_entry0_delta_l ..) σ τ (Fin.cases hf (Fin.cases hy (fun _ => hx)))).trans
        (rd_entry0_sat_l ec ..))

end YesMetaZFC.SetTheory.Internal

/-! ## 同一完整前驱图生产目标切片的传递性与配对闭包

所有目标元素都沿实际满图回到源切片。源内的配对见证经同一图送出，
其完整前驱方程保证目标配对没有额外成员；不要求源或目标模型满足 ZF。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

theorem rr_native_pair_l {N R P S Γ t : M.Domain}
    (nx : ∃ x, M.mem x N) (ny : ∃ y, M.mem y P)
    (B : (smdl_structure_l I (R := R) nx).Domain)
    (H : (smdl_structure_l I (R := S) ny).Domain)
    (pair : ∀ a b, (smdl_structure_l I (R := R) nx).mem a B →
      (smdl_structure_l I (R := R) nx).mem b B →
      ∃ p, (smdl_structure_l I (R := R) nx).mem p B ∧ Pair_d (smdl_structure_l I (R := R) nx) p a b)
    (carrier : ∀ x, M.mem x Γ ↔ M.mem x N ∧ M.PairMember I x B.val R)
    (ft : M.IsSetInjectionFromTo I t Γ P)
    (image : ∀ E, M.PairMember I E H.val S ↔ ∃ x, M.mem x Γ ∧ M.PairMember I x E t)
    (pred : ∀ x E, M.PairMember I x E t → ∀ y,
      M.PairMember I y E S ↔ ∃ a, M.PairMember I a x R ∧ M.PairMember I a y t) :
    (smdl_structure_l I (R := S) ny).TransitiveSet H ∧
      ∀ x y, (smdl_structure_l I (R := S) ny).mem x H → (smdl_structure_l I (R := S) ny).mem y H →
        ∃ p, (smdl_structure_l I (R := S) ny).mem p H ∧ Pair_d (smdl_structure_l I (R := S) ny) p x y := by
  let N₀ := smdl_structure_l I (R := R) nx
  constructor
  · intro x hx y hy
    obtain ⟨a,_,ia⟩ := (image x.val).mp hx
    obtain ⟨b,_,ib⟩ := (pred a x.val ia y.val).mp hy
    exact (image y.val).mpr ⟨b,ft.1.input_mem_of_pairMember ib,ib⟩
  · intro x y hx hy
    obtain ⟨a,ha,ia⟩ := (image x.val).mp hx
    obtain ⟨b,hb,ib⟩ := (image y.val).mp hy
    let a₀ : N₀.Domain := ⟨a,((carrier a).mp ha).1⟩
    let b₀ : N₀.Domain := ⟨b,((carrier b).mp hb).1⟩
    obtain ⟨p,hp,pairp⟩ := pair a₀ b₀ ((carrier a).mp ha).2 ((carrier b).mp hb).2
    obtain ⟨q,hq,ip⟩ := ft.1.2.2 p.val ((carrier p.val).mpr ⟨p.property,hp⟩)
    refine ⟨⟨q,hq⟩,(image q).mpr ⟨p.val,ft.1.input_mem_of_pairMember ip,ip⟩,fun z => ?_⟩
    constructor
    · intro hz
      obtain ⟨v,hv,iv⟩ := (pred p.val q ip z.val).mp hz
      let v₀ : N₀.Domain := ⟨v,((carrier v).mp (ft.1.input_mem_of_pairMember iv)).1⟩
      rcases (pairp v₀).mp hv with eq | eq
      · have eq : v = a := congrArg Subtype.val eq
        exact Or.inl (Subtype.ext (ft.1.1.2 a z.val x.val (eq ▸ iv) ia))
      · have eq : v = b := congrArg Subtype.val eq
        exact Or.inr (Subtype.ext (ft.1.1.2 b z.val y.val (eq ▸ iv) ib))
    · rintro (rfl | rfl)
      · exact (pred p.val q ip z.val).mpr ⟨a,(pairp a₀).mpr (Or.inl rfl),ia⟩
      · exact (pred p.val q ip z.val).mpr ⟨b,(pairp b₀).mpr (Or.inr rfl),ib⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 所属模型的有界可数闭性回收到原秩切片

先在所属模型中实现给定背景序列，再以原关系收集界回收值域和整张函数图。
切片的全部前驱保留有界函数公式，故同一函数对象实现切片中的原序列。
所属模型只用实际配对解释及外延性；不增加原生 ZF 或整体坍塌前提。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hKP : M.Models KP)
local notation "I" => kp_pair_l hKP

/-- 有界外部序列先成为所属模型的函数，再由同一收集界回到目标秩层。 -/
theorem Sc_bounded_omega_closed_d.capture_l {ω N R z f : M.Domain}
    (hω : M.IsOmega ω) (nx : ∃ x, M.mem x N)
    (J : kpair_convention_l.Interpretation (smdl_structure_l I (R := R) nx))
    (ext : Rf_ext_d I N R) (w δ U : (smdl_structure_l I (R := R) nx).Domain)
    (numbers : Rr_layer_d I ω N R w.val z) (rank : V_d J δ U)
    (limit : (smdl_structure_l I (R := R) nx).IsLimitOrdinal δ)
    (bound : Sc_bound_d U) (hw : (smdl_structure_l I (R := R) nx).mem w U)
    (closed : Sc_bounded_omega_closed_d I ω N R) (ff : Fn0_d ω N f)
    (values : ∀ n x, Rd_entry_d n x f → M.PairMember I x U.val R) :
    ∃ F B : (smdl_structure_l I (R := R) nx).Domain,
      (smdl_structure_l I (R := R) nx).mem F U ∧ (smdl_structure_l I (R := R) nx).mem B U ∧
      Fn0_d w B F ∧ Rc_graph_d I N R z F.val f := by
  let P := smdl_structure_l I (R := R) nx
  have en := ext.native_l I nx
  obtain ⟨g, fg, graph⟩ := closed.at_l I hKP hω ext numbers U.val f U.property ff values
  let F : P.Domain := ⟨g, fg.mem_l I⟩
  obtain ⟨B, fb⟩ := (rf_fun_native_l I nx en w F).mp fg
  have fu : Fn0_d w U F := fb.retarget_l (fun x y hxy => by
    obtain ⟨n, _, hnx⟩ := (numbers.image x.val).mp (fb.bound_l hxy).1
    exact values n y.val ((graph n x.val y.val hnx).mpr ((rf_val_native_l I nx en x y F).mpr hxy)))
  obtain ⟨hf, B', hb, fn⟩ := bound.function_l J rank limit hw fu
  exact ⟨F, B', hf, hb, fn, graph⟩

theorem Sc_bounded_omega_closed_d.cut_l {ω N R D S z : M.Domain}
    (hω : M.IsOmega ω) (nx : ∃ x, M.mem x N)
    (J : kpair_convention_l.Interpretation (smdl_structure_l I (R := R) nx))
    (ext : Rf_ext_d I N R) (w δ U : (smdl_structure_l I (R := R) nx).Domain)
    (numbers : Rr_layer_d I ω N R w.val z) (rank : V_d J δ U)
    (limit : (smdl_structure_l I (R := R) nx).IsLimitOrdinal δ)
    (bound : Sc_bound_d U) (hw : (smdl_structure_l I (R := R) nx).mem w U)
    (carrier : ∀ x, M.mem x D ↔ M.mem x N ∧ M.PairMember I x U.val R)
    (relation : ∀ x y, M.PairMember I x y S ↔ M.mem x D ∧ M.mem y D ∧ M.PairMember I x y R)
    (cut : Rr_layer_d I ω D S w.val z) (closed : Sc_bounded_omega_closed_d I ω N R) :
    Sc_omega_closed_d I ω D S := by
  let P := smdl_structure_l I (R := R) nx
  have en := ext.native_l I nx
  have ut := v_transitive_l J rank
  let nu : Nonempty {x : P.Domain // P.mem x U} := ⟨⟨w, hw⟩⟩
  let E := rt_model_l U nu
  let ny : ∃ x, M.mem x D := ⟨w.val, cut.member⟩
  let Q := smdl_structure_l I (R := S) ny
  have ee := rt_model_ext_l en ut nu
  have own (x : P.Domain) (hx : P.mem x U) : M.mem x.val D := (carrier x.val).mpr ⟨x.property, hx⟩
  let l : E.Domain → Q.Domain := fun x => ⟨x.val.val, own x.val x.property⟩
  refine ⟨w.val, z, cut, fun f ff => ?_⟩
  have wide := ff.mono_target_l (fun x hx => ((carrier x).mp hx).1)
  obtain ⟨F, B', hf, hb, fn, graph⟩ := closed.capture_l hKP hω nx J ext w δ U numbers rank limit bound hw wide
    (fun n x hnx => ((carrier x).mp (ff.bound_l hnx).2).2)
  let g := F.val
  let a : E.Domain := ⟨w, hw⟩
  let b : E.Domain := ⟨B', hb⟩
  let t : E.Domain := ⟨F, hf⟩
  let ρ : Env E 3 := ⟨Fin.cases a (Fin.cases b (fun _ => t)), fun _ => t⟩
  let σ : Env Q 3 := ⟨Fin.cases (l a) (Fin.cases (l b) (fun _ => l t)), fun _ => l t⟩
  have native := (fn0_sat_l ee ρ .newest (.bound 1) (.bound 2)).mpr ((rt_fn_l ut nu en a b t).mpr fn)
  have transfer := (rr_cut_formula_l I nx U nu ny carrier relation (fn0_m .newest (.bound 1) (.bound 2)) ρ).mp native
  have moved : Formula.satisfies σ (fn0_m .newest (.bound 1) (.bound 2)) :=
    (Formula.closed_env_l _ (by simp -implicitDefEqProofs) (ρ := image_env_l l ρ) (η := σ)
      (funext (Fin.cases rfl (Fin.cases rfl (fun _ => rfl))))).mp transfer
  have value (x y : P.Domain) (hx : P.mem x U) (hy : P.mem y U) :
      Rf_val_d I D S x.val y.val g ↔ Rd_entry_d x y F := by
    let η : Env E 3 := ⟨Fin.cases ⟨x, hx⟩ (Fin.cases ⟨y, hy⟩ (fun _ => t)), fun _ => t⟩
    let ε : Env P 3 := ⟨Fin.cases x (Fin.cases y (fun _ => F)), fun _ => F⟩
    let τ : Env Q 3 := ⟨Fin.cases (l ⟨x, hx⟩) (Fin.cases (l ⟨y, hy⟩) (fun _ => l t)), fun _ => l t⟩
    let φ : Formula 1 3 := rd_entry0_m .newest (.bound 1) (.bound 2)
    have delta : φ.IsDelta0 := rd_entry0_delta_l ..
    have relative : Formula.satisfies η φ ↔ Formula.satisfies ε φ :=
      rt_model_delta_l (M := P) ut nu delta η
    have absolute : Formula.satisfies η φ ↔ Rd_entry_d x y F :=
      relative.trans (rd_entry0_sat_l en ε .newest (.bound 1) (.bound 2))
    have equal : Formula.satisfies (image_env_l l η) φ ↔ Formula.satisfies τ φ :=
      Formula.closed_env_l φ (by simp -implicitDefEqProofs [φ])
        (funext (Fin.cases rfl (Fin.cases rfl (fun _ => rfl))))
    have read : Formula.satisfies τ φ ↔ Rd_entry_d x y F :=
      equal.symm.trans ((rr_cut_formula_l I nx U nu ny carrier relation φ η).symm.trans absolute)
    exact ⟨fun ⟨_, _, _, h⟩ => read.mp h, fun h => ⟨own x hx, own y hy, own F hf, read.mpr h⟩⟩
  refine ⟨g, ⟨own w hw, own F hf, ⟨B'.val, own B' hb⟩, moved⟩, ?_⟩
  intro n x y hnx
  have hx := (carrier x).mp (cut.injection.1.output_mem_of_pairMember hnx)
  by_cases hy : M.mem y D
  · have hy' := (carrier y).mp hy
    let x' : P.Domain := ⟨x, hx.1⟩
    let y' : P.Domain := ⟨y, hy'.1⟩
    exact (graph n x y hnx).trans ((rf_val_native_l I nx en x' y' F).trans (value x' y' hx.2 hy'.2).symm)
  · exact iff_of_false (fun h => hy (ff.bound_l h).2) (fun h => hy (h.bounds_l I).2.1)

section Image
variable (hZF : M.Models ZF)
local notation "Kp" => kp_pair_l (ZF.modelsKP hZF)

/-- 同一完整前驱图把秩层中的可数函数实现为新高模型中的函数；其对象仍属于新共同层。 -/
theorem Sc_bounded_omega_closed_d.image_l
    {ω N R D C S z z' w' H k : M.Domain}
    (hω : M.IsOmega ω) (nx : ∃ x, M.mem x N)
    (J : kpair_convention_l.Interpretation (smdl_structure_l Kp (R := R) nx))
    (ext : Rf_ext_d Kp N R)
    (w δ U : (smdl_structure_l Kp (R := R) nx).Domain)
    (numbers : Rr_layer_d Kp ω N R w.val z) (rank : V_d J δ U)
    (limit : (smdl_structure_l Kp (R := R) nx).IsLimitOrdinal δ)
    (bound : Sc_bound_d U) (hw : (smdl_structure_l Kp (R := R) nx).mem w U)
    (carrier : ∀ x, M.mem x D ↔ M.mem x N ∧ Rd_entry_d x U.val R)
    (fk : M.IsSetInjectionFromTo Kp k D C)
    (full : ∀ y, Rd_entry_d y H S ↔ ∃ x, M.mem x D ∧ Rd_entry_d x y k)
    (pred : ∀ x y, Rd_entry_d x y k → ∀ v, Rd_entry_d v y S ↔ ∃ a, Rd_entry_d a x R ∧ Rd_entry_d a v k)
    (ec : Rf_ext_d Kp C S) (hw' : Rd_entry_d w.val w' k)
    (numeric : ∀ n x, Rd_entry_d n x z' ↔ ∃ m, Rd_entry_d n m z ∧ Rd_entry_d m x k)
    (closed : Sc_bounded_omega_closed_d Kp ω N R) :
    ∀ f, Fn0_d ω C f → (∀ n x, Rd_entry_d n x f → Rd_entry_d x H S) →
      ∃ F, Rd_entry_d F H S ∧ Rf_fun_d Kp C S w' F ∧
        Rc_graph_d Kp C S z' F f := by
  let P := smdl_structure_l Kp (R := R) nx
  have en := ext.native_l Kp nx
  let ny : ∃ x, M.mem x C := ⟨w', fk.1.output_mem_of_pairMember hw'⟩
  let Q := smdl_structure_l Kp (R := S) ny
  have et := ec.native_l Kp ny
  intro f ff inside
  let ρ : Env M 2 := ⟨Fin.cases f (fun _ => k), fun _ => ω⟩
  let φ : BinarySchema 2 := { body := .existsE (.conj
    (rd_entry0_m (.bound 2) .newest (.bound 3)) (rd_entry0_m (.bound 1) .newest (.bound 4))) }
  have read n x : φ.denote ρ n x ↔ ∃ y, Rd_entry_d n y f ∧ Rd_entry_d x y k := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, rd_entry0_sat_l hZF.1]; rfl
  obtain ⟨g, fg, graph⟩ := ZF.exists_setFunctionFromTo_of_denote hZF Kp φ ρ (source := ω) (target := D)
    (fun n hn => by
      obtain ⟨y, _, hny⟩ := ff.2.1 n hn
      obtain ⟨x, _, hxy⟩ := (full y).mp (inside n y hny)
      exact ⟨x, (read n x).mpr ⟨y, hny, hxy⟩⟩)
    (fun n hn x y hx hy => by
      obtain ⟨a, hna, hxa⟩ := (read n x).mp hx
      obtain ⟨b, hnb, hyb⟩ := (read n y).mp hy
      have same := ff.2.2 n hn a (ff.bound_l hna).2 b (ff.bound_l hnb).2 hna hnb
      exact fk.2 x y a hxa (same.symm ▸ hyb))
    (fun n x _ hx => ((read n x).mp hx).elim fun y hy => fk.1.input_mem_of_pairMember hy.2)
  have fg' := fn0_of_function_l (ZF.modelsKP hZF) fg
  have values n x (hnx : Rd_entry_d n x g) := (read n x).mp ((graph n x).mp hnx).2
  obtain ⟨F, B, hf, hb, fn, original⟩ := closed.capture_l (ZF.modelsKP hZF) hω nx J ext w δ U numbers rank limit bound hw
    (fg'.mono_target_l (fun x hx => ((carrier x).mp hx).1))
    (fun n x hnx => ((carrier x).mp (fg'.bound_l hnx).2).2)
  have owned (x : P.Domain) (hx : P.mem x U) : M.mem x.val D := (carrier x.val).mpr ⟨x.property, hx⟩
  obtain ⟨F', hF', hFF⟩ := fk.1.2.2 F.val (owned F hf)
  obtain ⟨B', hB', hBB⟩ := fk.1.2.2 B.val (owned B hb)
  let a : Q.Domain := ⟨w', fk.1.output_mem_of_pairMember hw'⟩
  let b : Q.Domain := ⟨B', hB'⟩
  let t : Q.Domain := ⟨F', hF'⟩
  have lift := rr_native_function_l Kp nx ny en et U (v_transitive_l J rank) carrier fk pred
    w B F a b t hw' hBB hFF fn
  have ft := (rf_fun_native_l Kp ny et a t).mpr ⟨b, lift.1⟩
  refine ⟨F', (full F').mpr ⟨F.val, owned F hf, hFF⟩, ft, ?_⟩
  intro n x y hnx
  obtain ⟨m, hnm, hmx⟩ := (numeric n x).mp hnx
  have hn := numbers.injection.1.input_mem_of_pairMember hnm
  obtain ⟨v, hv, hnv⟩ := fg'.2.1 n hn
  obtain ⟨E, hnE, hvE⟩ := values n v hnv
  let m₀ : P.Domain := ⟨m, numbers.injection.1.output_mem_of_pairMember hnm⟩
  let v₀ : P.Domain := ⟨v, ((carrier v).mp hv).1⟩
  let x₀ : Q.Domain := ⟨x, fk.1.output_mem_of_pairMember hmx⟩
  let E₀ : Q.Domain := ⟨E, (ff.bound_l hnE).2⟩
  have old := (rf_val_native_l Kp nx en m₀ v₀ F).mp ((original n m v hnm).mp hnv)
  have next := (rf_val_native_l Kp ny et x₀ E₀ t).mpr ((lift.2 m₀ v₀ x₀ E₀ hmx hvE).mp old)
  exact ⟨fun hny => (ff.2.2 n hn y (ff.bound_l hny).2 E (ff.bound_l hnE).2 hny hnE).symm ▸ next,
    fun hy => (ft.unique_l Kp ec hy next).symm ▸ hnE⟩

end Image

end YesMetaZFC.SetTheory.Internal
