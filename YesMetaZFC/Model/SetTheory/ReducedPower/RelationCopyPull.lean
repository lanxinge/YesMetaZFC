import YesMetaZFC.Model.SetTheory.ReducedPower.RelationNormalize
import YesMetaZFC.Model.SetTheory.Relations.CollectCode
import YesMetaZFC.Model.SetTheory.Relations.CompositionGraph

/-! # 原关系代表族的一阶规格

规格保留内部函数码及其实际坐标图，供全部支撑的一次替换使用。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

def Rc_family_d (Y S D d t G : M.Domain) : Prop := ∀ g, M.mem g G ↔ Fn0_d D Y g ∧
  ∃ f, Rf_fun_d I Y S d f ∧ Rc_graph_d I Y S t f g

def rc_family_m {n} (Y S D d t G : Term n) : Formula 1 n := .forallE
  (.iff (.mem .newest G.weaken) (.conj (fn0_m D.weaken Y.weaken .newest) (.existsE
    (.conj (rf_fun_m (𝒞 := kpair_convention_l) Y.weaken.weaken S.weaken.weaken d.weaken.weaken .newest)
      (rc_graph_m (𝒞 := kpair_convention_l) Y.weaken.weaken S.weaken.weaken t.weaken.weaken .newest (.bound 1))))))
derive_free_closed rc_family_m

theorem rc_family_sat_l (hE : Extensional M) {n} (ρ : Env M n) (Y S D d t G : Term n) :
    Formula.satisfies ρ (rc_family_m Y S D d t G) ↔
      Rc_family_d I (Y.eval ρ) (S.eval ρ) (D.eval ρ) (d.eval ρ) (t.eval ρ) (G.eval ρ) := by
  simp only [rc_family_m, Rc_family_d, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_conj_iff, fn0_sat_l hE,
    Formula.satisfies_exists_iff, rf_fun_sat_l I, rc_graph_sat_l I hE, Definitional.Term.eval_weaken]; rfl

theorem rc_family_native_l {Y S D t G : M.Domain} (ny : ∃ y, M.mem y Y)
    (en : Extensional (smdl_structure_l I (R := S) ny))
    (d : (smdl_structure_l I (R := S) ny).Domain) (ft : Fn0_d D Y t) :
    Rc_family_d I Y S D d.val t G ↔ ∀ g, M.mem g G ↔ Fn0_d D Y g ∧
      ∃ B f : (smdl_structure_l I (R := S) ny).Domain, Fn0_d d B f ∧
        ∀ s (x y : (smdl_structure_l I (R := S) ny).Domain), Rd_entry_d s x.val t →
          (Rd_entry_d s y.val g ↔ Rd_entry_d x y f) := by
  have read g (fg : Fn0_d D Y g) :
      (∃ f, Rf_fun_d I Y S d.val f ∧ Rc_graph_d I Y S t f g) ↔
        ∃ B f : (smdl_structure_l I (R := S) ny).Domain, Fn0_d d B f ∧
          ∀ s (x y : (smdl_structure_l I (R := S) ny).Domain), Rd_entry_d s x.val t →
            (Rd_entry_d s y.val g ↔ Rd_entry_d x y f) := by
    constructor
    · rintro ⟨f, ff, graph⟩
      obtain ⟨B, fb⟩ := (rf_fun_native_l I ny en d ⟨f, ff.mem_l I⟩).mp ff
      exact ⟨B, ⟨f, ff.mem_l I⟩, fb, (rc_graph_native_l I ny en ft fg _).mp graph⟩
    · rintro ⟨B, f, ff, graph⟩
      exact ⟨f.val, (rf_fun_native_l I ny en d f).mpr ⟨B, ff⟩, (rc_graph_native_l I ny en ft fg f).mpr graph⟩
  exact forall_congr' fun g => iff_congr Iff.rfl (and_congr_right (read g))

end YesMetaZFC.SetTheory.Internal

/-! ## 原函数码赋值的唯一商像

先展开已给函数码，再应用既有商投影。两步均由唯一性收集，
不在商类中选择代表，也不要求原关系模型满足替换或选择。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

theorem Rc_graph_d.unique_l (hE : Extensional M) {Y S D t f g g' : M.Domain}
    (ft : Fn0_d D Y t) (fg : Fn0_d D Y g) (fg' : Fn0_d D Y g')
    (h : Rc_graph_d I Y S t f g) (h' : Rc_graph_d I Y S t f g') : g = g' := by
  apply fg.ext_l hE fg'
  intro s hs
  obtain ⟨x, _, hsx⟩ := ft.2.1 s hs
  obtain ⟨y, _, hsy⟩ := fg.2.1 s hs
  exact ⟨y, hsy, (h' s x y hsx).mpr ((h s x y hsx).mp hsy)⟩

variable (hZF : M.Models ZF)
local notation "Kp" => kp_pair_l (ZF.modelsKP hZF)

theorem rc_eval_exists_l {ω Y S D t G p C a : M.Domain}
    (ny : ∃ y, M.mem y Y) (ext : Extensional (smdl_structure_l Kp (R := S) ny))
    (d : (smdl_structure_l Kp (R := S) ny).Domain) (ft : Fn0_d D Y t)
    (domain : ∀ s x, Rd_entry_d s x t → Rd_entry_d x d.val S)
    (family : Rc_family_d Kp Y S D d.val t G) (hp : M.IsSetFunctionFromTo Kp p G C)
    (ha : M.IsSetFunctionFromTo Kp a ω Y) (repr : Pe_repr_d Kp ω d.val Y S a) :
    ∃ v, M.IsSetFunctionFromTo Kp v ω C ∧ Rc_eval_d Kp ω d.val Y S t p a v := by
  let ρ : Env M 6 := ⟨Fin.cases Y (Fin.cases S (Fin.cases t
    (Fin.cases G (Fin.cases p (fun _ => a))))), fun _ => Y⟩
  let φ : BinarySchema 6 := { body := Formula.existsMem (.bound 2) (Formula.existsMem (.bound 6)
    (.conj (rd_entry0_m (.bound 3) (.bound 1) (.bound 9))
      (.conj (rc_graph_m (𝒞 := kpair_convention_l) (.bound 4) (.bound 5) (.bound 6) (.bound 1) .newest)
        (rd_entry0_m .newest (.bound 2) (.bound 8))))) }
  have read i B : φ.denote ρ i B ↔ ∃ f, M.mem f Y ∧ ∃ g, M.mem g G ∧
      Rd_entry_d i f a ∧ Rc_graph_d Kp Y S t f g ∧ Rd_entry_d g B p := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
      rd_entry0_sat_l hZF.1, rc_graph_sat_l Kp hZF.1]; rfl
  obtain ⟨v, fv, graph⟩ := ZF.exists_setFunctionFromTo_of_denote hZF Kp φ ρ (source := ω) (target := C)
    (fun i hi => by
      obtain ⟨f, hf, hif⟩ := ha.2.2 i hi
      have ff := repr i f hi hif
      obtain ⟨B, fn⟩ := (rf_fun_native_l Kp ny ext d ⟨f, hf⟩).mp ff
      obtain ⟨g, fg, decode⟩ := smdl_function_l hZF ny ext d B ⟨f, hf⟩ fn ft domain
      have gr := (rc_graph_native_l Kp ny ext ft fg ⟨f, hf⟩).mpr decode
      have hg := (family g).mpr ⟨fg, f, ff, gr⟩
      obtain ⟨b, _, hgb⟩ := hp.2.2 g hg
      exact ⟨b, (read i b).mpr ⟨f, hf, g, hg, hif, gr, hgb⟩⟩)
    (fun i _ b c hb hc => by
      obtain ⟨f, _, g, hg, hif, gr, hgb⟩ := (read i b).mp hb
      obtain ⟨f', _, g', hg', hif', gr', hgc⟩ := (read i c).mp hc
      have eq := ha.1.2 i f' f hif' hif
      have eg := gr.unique_l Kp hZF.1 ft ((family g).mp hg).1 ((family g').mp hg').1 (eq ▸ gr')
      exact hp.1.2 g b c hgb (eg.symm ▸ hgc))
    (fun i B _ h => by
      obtain ⟨_, _, g, _, _, _, hgB⟩ := (read i B).mp h
      exact hp.output_mem_of_pairMember hgB)
  refine ⟨v, fv, fun i hi => ?_⟩
  obtain ⟨B, _, hiB⟩ := fv.2.2 i hi
  obtain ⟨f, _, g, _, hif, gr, hgB⟩ := (read i B).mp ((graph i B).mp hiB).2
  exact ⟨f, g, B, hif, repr i f hi hif, gr, hgB, hiB⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 原关系函数码沿初等图的实际复制

完整定义域坐标唯一决定源函数码。先搬运这个码，再在目标的完整定义域
展开其实际图；新定义域不必由旧坐标的像穷尽，也不要求两边已经坍塌。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

/-- 覆盖全部原定义域的求值图唯一确定函数码。 -/
theorem Rc_graph_d.code_unique_l {X R t d f f' g : M.Domain}
    (nx : ∃ x, M.mem x X) (ext : Rf_ext_d I X R)
    (onto : ∀ x, M.PairMember I x d R → ∃ s, Rd_entry_d s x t)
    (ff : Rf_fun_d I X R d f) (ff' : Rf_fun_d I X R d f')
    (graph : Rc_graph_d I X R t f g) (graph' : Rc_graph_d I X R t f' g) : f = f' := by
  let N := smdl_structure_l I (R := R) nx
  have en := ext.native_l I nx
  let D : N.Domain := ⟨d, ff.1⟩
  let F : N.Domain := ⟨f, ff.mem_l I⟩
  let F' : N.Domain := ⟨f', ff'.mem_l I⟩
  obtain ⟨B, hf⟩ := (rf_fun_native_l I nx en D F).mp ff
  obtain ⟨B', hf'⟩ := (rf_fun_native_l I nx en D F').mp ff'
  apply congrArg Subtype.val (hf.ext_l en hf' ?_)
  intro x hx
  obtain ⟨y, _, hxy⟩ := hf.2.1 x hx
  obtain ⟨s, hs⟩ := onto x.val hx
  exact ⟨y, hxy, (rf_val_native_l I nx en x y F').mp ((graph' s x.val y.val hs).mp
    ((graph s x.val y.val hs).mpr ((rf_val_native_l I nx en x y F).mpr hxy)))⟩

def Rc_copy_d (X R d t Y S u π g h : M.Domain) : Prop := ∃ f f',
  Rf_fun_d I X R d f ∧ Rc_graph_d I X R t f g ∧ Rd_entry_d f f' π ∧ Rc_graph_d I Y S u f' h

def rc_copy_m {n} (X R d t Y S u π g h : Term n) : Formula 1 n := set[n] ⟪∃ f f',
  ⌜rf_fun_m (𝒞 := kpair_convention_l)⌝ₚ(⌜X⌝ₛ, ⌜R⌝ₛ, ⌜d⌝ₛ, f) ∧
  ⌜rc_graph_m (𝒞 := kpair_convention_l)⌝ₚ(⌜X⌝ₛ, ⌜R⌝ₛ, ⌜t⌝ₛ, f, ⌜g⌝ₛ) ∧
  ⌜rd_entry0_m⌝ₚ(f, f', ⌜π⌝ₛ) ∧
  ⌜rc_graph_m (𝒞 := kpair_convention_l)⌝ₚ(⌜Y⌝ₛ, ⌜S⌝ₛ, ⌜u⌝ₛ, f', ⌜h⌝ₛ)⟫
derive_free_closed rc_copy_m

theorem rc_copy_sat_l (hE : Extensional M) {n} (ρ : Env M n) (X R d t Y S u π g h : Term n) :
    Formula.satisfies ρ (rc_copy_m X R d t Y S u π g h) ↔
      Rc_copy_d I (X.eval ρ) (R.eval ρ) (d.eval ρ) (t.eval ρ) (Y.eval ρ) (S.eval ρ)
        (u.eval ρ) (π.eval ρ) (g.eval ρ) (h.eval ρ) := by
  simp only [rc_copy_m, Rc_copy_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    rf_fun_sat_l I, rc_graph_sat_l I hE, rd_entry0_sat_l hE, Definitional.Term.eval_weaken]; rfl

variable (hZF : M.Models ZF)
local notation "Kp" => kp_pair_l (ZF.modelsKP hZF)

/-- 原代表族中的每个实际图，自动复制为目标原代表族中的实际图。 -/
theorem rc_copy_family_l {ω c a X R Y S π D E d e t u G H : M.Domain}
    (hω : M.IsOmega ω) (mx : Smdl_d Kp c X R) (my : Smdl_d Kp a Y S)
    (map : Smap_d Kp ω c a X Y π) (ext : Rf_ext_d Kp X R) (hd : Rd_entry_d d e π)
    (fu : Fn0_d E Y u)
    (onto : ∀ x, Rd_entry_d x d R → ∃ s, Rd_entry_d s x t)
    (domain : ∀ s x, Rd_entry_d s x u → Rd_entry_d x e S)
    (source : Rc_family_d Kp X R D d t G) (target : Rc_family_d Kp Y S E e u H) :
    ∃ K, M.IsSetFunctionFromTo Kp K G H ∧ ∀ g h, Rd_entry_d g h K ↔
      M.mem g G ∧ M.mem h H ∧ Rc_copy_d Kp X R d t Y S u π g h := by
  have ey₀ : Rf_ext_d Kp Y S := map.extensional_l hZF hω mx my ext
  have ey := ey₀.native_l Kp my.2.1
  have make g (hg : M.mem g G) : ∃ h, M.mem h H ∧ Rc_copy_d Kp X R d t Y S u π g h := by
    obtain ⟨_, f, ff, graph⟩ := (source g).mp hg
    obtain ⟨f', hf', hff⟩ := map.1.1.2.2 f (ff.mem_l Kp)
    have fn := ff.map_l Kp hZF hω mx my map hd hff
    let e₀ : (smdl_structure_l Kp (R := S) my.2.1).Domain := ⟨e, map.1.1.output_mem_of_pairMember hd⟩
    let F : (smdl_structure_l Kp (R := S) my.2.1).Domain := ⟨f', hf'⟩
    obtain ⟨B, fb⟩ := (rf_fun_native_l Kp my.2.1 ey e₀ F).mp fn
    obtain ⟨h, fh, decode⟩ := smdl_function_l hZF my.2.1 ey e₀ B F fb fu domain
    have graph' := (rc_graph_native_l Kp my.2.1 ey fu fh F).mpr decode
    exact ⟨h, (target h).mpr ⟨fh, f', fn, graph'⟩, f, f', ff, graph, hff, graph'⟩
  have unique g h k (hh : M.mem h H) (hk : M.mem k H)
      (a : Rc_copy_d Kp X R d t Y S u π g h) (b : Rc_copy_d Kp X R d t Y S u π g k) : h = k := by
    obtain ⟨f, f', ff, graph, hff, graph'⟩ := a
    obtain ⟨v, v', fv, code, hvv, code'⟩ := b
    have eq := graph.code_unique_l Kp mx.2.1 ext onto ff fv code
    subst v
    have eq := map.1.1.1.2 f v' f' hvv hff
    subst v'
    exact graph'.unique_l Kp hZF.1 fu ((target h).mp hh).1 ((target k).mp hk).1 code'
  let ρ : Env M 9 := ⟨Fin.cases X (Fin.cases R (Fin.cases d (Fin.cases t
    (Fin.cases Y (Fin.cases S (Fin.cases u (Fin.cases π (fun _ => H)))))))), fun _ => X⟩
  let φ : BinarySchema 9 := { body := .conj (.mem .newest (.bound 10)) (rc_copy_m
    (.bound 2) (.bound 3) (.bound 4) (.bound 5) (.bound 6) (.bound 7) (.bound 8) (.bound 9) (.bound 1) .newest) }
  have sat g h : φ.denote ρ g h ↔ M.mem h H ∧ Rc_copy_d Kp X R d t Y S u π g h := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff, rc_copy_sat_l Kp hZF.1]; rfl
  obtain ⟨K, fn, spec⟩ := ZF.exists_setFunctionFromTo_of_denote hZF Kp φ ρ (source := G) (target := H)
    (fun g hg => (make g hg).imp fun h hh => (sat g h).mpr hh)
    (fun g _ h k hh hk => unique g h k ((sat g h).mp hh).1 ((sat g k).mp hk).1
      ((sat g h).mp hh).2 ((sat g k).mp hk).2)
    (fun g h _ hh => ((sat g h).mp hh).1)
  exact ⟨K, fn, fun g h => (spec g h).trans (and_congr_right fun _ => sat g h)⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 原坐标代表在复制下的精确像

源坐标代表给出内部恒等函数的方程。完整初等性把这一全称方程搬到
目标的全部坐标，再由函数图外延性识别目标代表，无需先坍塌任一模型。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Rc_copy_d.coordinate_l {ω c a X R Y S π E d e t u g : M.Domain}
    (hω : M.IsOmega ω) (mx : Smdl_d I c X R) (my : Smdl_d I a Y S)
    (map : Smap_d I ω c a X Y π) (ext : Rf_ext_d I X R)
    (hd : Rd_entry_d d e π) (fu : Fn0_d E Y u) (fg : Fn0_d E Y g)
    (onto : ∀ x, Rd_entry_d x d R → ∃ s, Rd_entry_d s x t)
    (domain : ∀ s x, Rd_entry_d s x u → Rd_entry_d x e S)
    (copy : Rc_copy_d I X R d t Y S u π t g) : g = u := by
  obtain ⟨f, f', _, graph, hff, graph'⟩ := copy
  have ex := ext.native_l I mx.2.1
  have ext' : Rf_ext_d I Y S := map.extensional_l hZF hω mx my ext
  have ey := ext'.native_l I my.2.1
  let d₀ : (smdl_structure_l I (R := R) mx.2.1).Domain := ⟨d, map.1.1.input_mem_of_pairMember hd⟩
  let d₁ : (smdl_structure_l I (R := S) my.2.1).Domain := ⟨e, map.1.1.output_mem_of_pairMember hd⟩
  let f₀ : (smdl_structure_l I (R := R) mx.2.1).Domain := ⟨f, map.1.1.input_mem_of_pairMember hff⟩
  let f₁ : (smdl_structure_l I (R := S) my.2.1).Domain := ⟨f', map.1.1.output_mem_of_pairMember hff⟩
  let φ : Formula 1 2 := Formula.forallMem (.bound 1) (rd_entry0_m .newest .newest (.bound 1))
  let ρ : Env (smdl_structure_l I (R := R) mx.2.1) 2 := ⟨Fin.cases f₀ (fun _ => d₀), fun _ => d₀⟩
  let η : Env (smdl_structure_l I (R := S) my.2.1) 2 := ⟨Fin.cases f₁ (fun _ => d₁), fun _ => d₁⟩
  have tr := smap_source_l I hZF hω mx my map φ (by simp -implicitDefEqProofs [φ]) ρ η
    (Fin.cases hff (fun _ => hd))
  simp only [φ, Formula.satisfies_forallMem_iff, rd_entry0_sat_l ex, rd_entry0_sat_l ey] at tr
  have diagonal := tr.mp (fun x hx => by
    obtain ⟨s, hsx⟩ := onto x.val hx
    exact (rf_val_native_l I mx.2.1 ex x x f₀).mp ((graph s x.val x.val hsx).mp hsx))
  apply fg.ext_l hZF.1 fu
  intro s hs
  obtain ⟨x, hx, hsx⟩ := fu.2.1 s hs
  exact ⟨x, (graph' s x x hsx).mpr ((rf_val_native_l I my.2.1 ey ⟨x, hx⟩ ⟨x, hx⟩ f₁).mpr
    (diagonal ⟨x, hx⟩ (domain s x hsx))), hsx⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 原关系代表复制与坐标拉回交换

完整坐标先把实际拉回方程读回原函数码。以有限重排函数图表述这个方程，
沿完整初等图搬运后，直接读出目标全部坐标上的代表复合。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 以有限重排图表述投影，完整初等性覆盖目标定义域的全部新坐标。 -/
theorem rc_copy_pull_l
    {ω c X R c' Y S π D E D' E' d e d' e' u v u' v' t t' r r' g h g' h' : M.Domain}
    (hω : M.IsOmega ω) (mx : Smdl_d I c X R) (my : Smdl_d I c' Y S)
    (map : Smap_d I ω c c' X Y π) (ext : Rf_ext_d I X R)
    (hd : Rd_entry_d d d' π) (he : Rd_entry_d e e' π) (hr : Rd_entry_d r r' π)
    (ft : Fn0_d E D t)
    (fu' : Fn0_d D' Y u') (fv' : Fn0_d E' Y v') (ft' : Fn0_d E' D' t')
    (fg : Fn0_d D X g) (fg' : Fn0_d D' Y g') (fh' : Fn0_d E' Y h')
    (ontoD : ∀ x, Rd_entry_d x d R → ∃ s, Rd_entry_d s x u)
    (ontoE : ∀ x, Rd_entry_d x e R → ∃ s, Rd_entry_d s x v)
    (domD : ∀ s x, Rd_entry_d s x u' → Rd_entry_d x d' S)
    (domE : ∀ s x, Rd_entry_d s x v' → Rd_entry_d x e' S)
    (read : ∀ s q x y, Rd_entry_d s x v → Rd_entry_d q y u →
      (Rd_entry_d s q t ↔ Rf_comp_d I X R r x y))
    (read' : ∀ s q x y, Rd_entry_d s q t' → Rd_entry_d s x v' → Rd_entry_d q y u' →
      Rf_comp_d I Y S r' x y)
    (cg : Rc_copy_d I X R d u Y S u' π g g') (ch : Rc_copy_d I X R e v Y S v' π h h')
    (pull : Cp0_d E D X t g h) : Cp0_d E' D' Y t' g' h' := by
  obtain ⟨F, F', fF, gf, hFF, gf'⟩ := cg
  obtain ⟨H, H', fH, gh, hHH, gh'⟩ := ch
  have ext' : Rf_ext_d I Y S := map.extensional_l hZF hω mx my ext
  have ex := ext.native_l I mx.2.1
  have ey := ext'.native_l I my.2.1
  let F₀ : (smdl_structure_l I (R := R) mx.2.1).Domain := ⟨F, fF.mem_l I⟩
  let H₀ : (smdl_structure_l I (R := R) mx.2.1).Domain := ⟨H, fH.mem_l I⟩
  let r₀ : (smdl_structure_l I (R := R) mx.2.1).Domain := ⟨r, map.1.1.input_mem_of_pairMember hr⟩
  let d₀ : (smdl_structure_l I (R := R) mx.2.1).Domain := ⟨d, fF.1⟩
  let e₀ : (smdl_structure_l I (R := R) mx.2.1).Domain := ⟨e, fH.1⟩
  let F₁ : (smdl_structure_l I (R := S) my.2.1).Domain := ⟨F', map.1.1.output_mem_of_pairMember hFF⟩
  let H₁ : (smdl_structure_l I (R := S) my.2.1).Domain := ⟨H', map.1.1.output_mem_of_pairMember hHH⟩
  let r₁ : (smdl_structure_l I (R := S) my.2.1).Domain := ⟨r', map.1.1.output_mem_of_pairMember hr⟩
  let d₁ : (smdl_structure_l I (R := S) my.2.1).Domain := ⟨d', map.1.1.output_mem_of_pairMember hd⟩
  let e₁ : (smdl_structure_l I (R := S) my.2.1).Domain := ⟨e', map.1.1.output_mem_of_pairMember he⟩
  let ρ : Env (smdl_structure_l I (R := R) mx.2.1) 5 :=
    ⟨Fin.cases H₀ (Fin.cases F₀ (Fin.cases r₀ (Fin.cases e₀ (fun _ => d₀)))), fun _ => r₀⟩
  let η : Env (smdl_structure_l I (R := S) my.2.1) 5 :=
    ⟨Fin.cases H₁ (Fin.cases F₁ (Fin.cases r₁ (Fin.cases e₁ (fun _ => d₁)))), fun _ => r₁⟩
  -- 全称方程 H(s) = F(s ∘ r) 只以两个定义域和三个函数图为参数。
  let φ : Formula 1 5 := Formula.forallMem (.bound 3) (Formula.forallMem (.bound 5) (.forallE
    (.imp (cg_m (.bound 5) (.bound 2) (.bound 1))
      (.iff (rd_entry0_m (.bound 2) .newest (.bound 3)) (rd_entry0_m (.bound 1) .newest (.bound 4))))))
  have moved := smap_source_l I hZF hω mx my map φ
    (by simp -implicitDefEqProofs [φ, Formula.forallMem, Definitional.Formula.FreeClosed]) ρ η
    (Fin.cases hHH (Fin.cases hFF (Fin.cases hr (Fin.cases he (fun _ => hd)))))
  simp only [φ, Formula.satisfies_forallMem_iff, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_iff_iff, cg_sat_l ex, cg_sat_l ey, rd_entry0_sat_l ex, rd_entry0_sat_l ey] at moved
  have next := moved.mp (fun x hx y hy z comp => by
    obtain ⟨s, hsx⟩ := ontoE x.val hx
    obtain ⟨q, hqy⟩ := ontoD y.val hy
    have hsq := (read s q x.val y.val hsx hqy).mpr ((rf_comp_native_l I mx.2.1 ex r₀ x y).mpr comp)
    exact (rf_val_native_l I mx.2.1 ex x z H₀).symm.trans ((gh s x.val z.val hsx).symm.trans
      ((pull.value_l ft fg hsq).trans ((gf q y.val z.val hqy).trans (rf_val_native_l I mx.2.1 ex y z F₀)))))
  -- 在目标有限幂中任取 s，故此步同时覆盖并非原坐标像的新点。
  refine ⟨fh', fun s hs => ?_⟩
  obtain ⟨q, hq, hsq⟩ := ft'.2.1 s hs
  obtain ⟨x, hx, hsx⟩ := fv'.2.1 s hs
  obtain ⟨y, hy, hqy⟩ := fu'.2.1 q hq
  obtain ⟨z, hz, hqz⟩ := fg'.2.1 q hq
  let x₁ : (smdl_structure_l I (R := S) my.2.1).Domain := ⟨x, hx⟩
  let y₁ : (smdl_structure_l I (R := S) my.2.1).Domain := ⟨y, hy⟩
  let z₁ : (smdl_structure_l I (R := S) my.2.1).Domain := ⟨z, hz⟩
  have law := next x₁ (domE s x hsx) y₁ (domD q y hqy) z₁
    ((rf_comp_native_l I my.2.1 ey r₁ x₁ y₁).mp (read' s q x y hsq hsx hqy))
  have hzH := (rf_val_native_l I my.2.1 ey x₁ z₁ H₁).mpr
    (law.mpr ((rf_val_native_l I my.2.1 ey y₁ z₁ F₁).mp ((gf' q y z hqy).mp hqz)))
  exact ⟨q, hq, z, hz, hsq, hqz, (gh' s x z hsx).mpr hzH⟩

end YesMetaZFC.SetTheory.Internal
