import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawCopyClass
import YesMetaZFC.SetTheory.LargeCardinal.Extender.LocalRead
import YesMetaZFC.Model.SetTheory.ReducedPower.RelationCopyPull
import YesMetaZFC.SetTheory.MembershipInduction

/-! # 实际隶属源中的原关系支撑数据

传递性和已实现的有限闭包给出全部内部有限幂的精确解释。
实际商分量只消费共同图已经给出的有限幂对应，不要求其定义域是两源的整个交集。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}
section Space
variable (I : kpair_convention_l.Interpretation M) (ext : Extensional M)
include ext

/-- 有限闭包涵盖背景的所有内部有限长度，无须整个源满足 KP。 -/
theorem er_space_mem_l {ω c X R κ n D : M.Domain}
    (fs : Fs_read_d ω X) (mx : Smem_d I c X R) (hκ : M.mem κ X) (hn : M.mem n ω) :
    Er_space_d I X R κ n D ↔ M.mem D X ∧ Ep_space_d κ n D := by
  have hnx := fs.transitive ω fs.omega_mem n hn
  have read (hD : M.mem D X) : Er_space_d I X R κ n D ↔
      Ep_space_d (M := rt_model_l X ⟨⟨D, hD⟩⟩) ⟨κ, hκ⟩ ⟨n, hnx⟩ ⟨D, hD⟩ := by
    let v : Fin 3 → M.Domain := Fin.cases D (Fin.cases n (fun _ => κ))
    let hv : ∀ i, M.mem (v i) X := Fin.cases hD (Fin.cases hnx (fun _ => hκ))
    let ρ : Env (rt_model_l X ⟨⟨D, hD⟩⟩) 3 := ⟨fun i => ⟨v i, hv i⟩, fun _ => ⟨D, hD⟩⟩
    have tr := (smem_formula_l I mx ⟨⟨D, hD⟩⟩ (ep_space_m (.bound 2) (.bound 1) .newest) ρ).symm.trans
      (ep_space_sat_l (rt_model_ext_l ext fs.transitive ⟨⟨D, hD⟩⟩) ρ (.bound 2) (.bound 1) .newest)
    exact ⟨fun ⟨_, h⟩ => tr.mp h, fun h => ⟨hv, tr.mpr h⟩⟩
  constructor
  · intro h
    have hD := h.elim fun b _ => b 0
    have space := (read hD).mp h
    refine ⟨hD, fun s => ⟨fun hs => ?_, fun hs => ?_⟩⟩
    · exact (rt_fn_l fs.transitive ⟨⟨D, hD⟩⟩ ext ..).mp
        ((space ⟨s, fs.transitive D hD s hs⟩).mp hs)
    · exact (space ⟨s, fs.functions n κ s hn (fs.transitive κ hκ) hs⟩).mpr
        ((rt_fn_l fs.transitive ⟨⟨D, hD⟩⟩ ext ..).mpr hs)
  · rintro ⟨hD, space⟩
    exact (read hD).mpr (fun s => (space s.val).trans
      (rt_fn_l fs.transitive ⟨⟨D, hD⟩⟩ ext ⟨n, hnx⟩ ⟨κ, hκ⟩ s).symm)

end Space

section Agreement
variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 两个真实传递源的共同对象直接构成完整前驱图及全部有限幂子集对应。 -/
theorem Ea_agree_d.raw_l {ω c X R d Y S κ : M.Domain}
    (agree : Ea_agree_d ω κ X Y) (fs : Fs_read_d ω X) (hω : M.TransitiveSet ω)
    (mx : Smem_d I c X R) (my : Smem_d I d Y S) (hy : M.TransitiveSet Y)
    (hκ : M.mem κ X) (hκ' : M.mem κ Y) :
    ∃ z Γ k, Rr_layer_d I ω X R ω z ∧ Er_agree_d I ω X R κ z Γ Y S k ∧
      (∀ n m, Rd_entry_d n m z ↔ M.mem n ω ∧ n = m) ∧
      (∀ x, M.mem x Γ ↔ M.mem x X ∧ M.mem x Y) ∧
      ∀ x y, Rd_entry_d x y k ↔ M.mem x Γ ∧ x = y := by
  obtain ⟨z, numbers, zs⟩ := rr_layer_mem_l I hZF mx fs.transitive fs.omega_mem hω
  obtain ⟨Γ, gs⟩ := KP.intersection_exists_d (ZF.modelsKP hZF) X Y
  obtain ⟨k, fk, ks⟩ := fn0_identity_l (ZF.modelsKP hZF) Γ
  have inj : M.IsSetInjectionFromTo I k Γ Y :=
    ⟨fn0_function_l (ZF.modelsKP hZF) (fk.mono_target_l (fun x hx => ((gs x).mp hx).2)),
      fun x y v hx hy => ((ks x v).mp hx).2.trans ((ks y v).mp hy).2.symm⟩
  refine ⟨z, Γ, k, numbers, ⟨fun x hx => ((gs x).mp hx).1, ?_, inj, ?_,
    (gs κ).mpr ⟨hκ, hκ'⟩, ?_⟩, zs, gs, ks⟩
  · intro x y hx hyx hyR
    exact (gs y).mpr ⟨hyx, hy x ((gs x).mp hx).2 y ((mx.2 y x).mp hyR).2.2⟩
  · intro x y hxy v
    obtain ⟨hx, rfl⟩ := (ks x y).mp hxy
    have hxx := ((gs x).mp hx).1
    have hxy := ((gs x).mp hx).2
    constructor
    · intro hv
      have hvx := ((my.2 v x).mp hv).2.2
      exact ⟨v, (mx.2 v x).mpr ⟨fs.transitive x hxx v hvx, hxx, hvx⟩,
        (ks v v).mpr ⟨(gs v).mpr ⟨fs.transitive x hxx v hvx, hy x hxy v hvx⟩, rfl⟩⟩
    · rintro ⟨s, hs, hsv⟩
      obtain ⟨_, rfl⟩ := (ks s v).mp hsv
      have hsx := ((mx.2 s x).mp hs).2.2
      exact (my.2 s x).mpr ⟨hy x hxy s hsx, hxy, hsx⟩
  · intro n m D hn hnm space
    obtain ⟨_, rfl⟩ := (zs n m).mp hnm
    obtain ⟨hD, ds⟩ := (er_space_mem_l I hZF.1 fs mx hκ hn).mp space
    have hD' := (agree n D D hn ds (fun _ h => h)).mp hD
    refine ⟨D, (ks D D).mpr ⟨(gs D).mpr ⟨hD, hD'⟩, rfl⟩, ?_, ?_⟩
    · intro A hA sub
      have small x (hx : M.mem x A) := ((mx.2 x D).mp
        (sub x (fs.transitive A hA x hx) ((mx.2 x A).mpr ⟨fs.transitive A hA x hx, hA, hx⟩))).2.2
      exact (gs A).mpr ⟨hA, (agree n D A hn ds small).mp hA⟩
    · intro B hB sub
      have small y (hyB : M.mem y B) := ((my.2 y D).mp
        (sub y (hy B hB y hyB) ((my.2 y B).mpr ⟨hy B hB y hyB, hB, hyB⟩))).2.2
      exact ⟨B, (ks B B).mpr ⟨(gs B).mpr ⟨(agree n D B hn ds small).mpr hB, hB⟩, rfl⟩⟩

end Agreement

section Component
variable (hKP : M.Models KP)
local notation "I" => kp_pair_l hKP

/-- 实际商分量沿共同恒等图展开后，保留原代表族、原测度和原结构码。 -/
theorem Ep_component_d.raw_l {ω c X R d Y S κ L F a o z Γ k : M.Domain}
    (fs : Fs_read_d ω X) (mx : Smem_d I c X R) (my : Smem_d I d Y S)
    (hy : M.TransitiveSet Y) (algebra : Sc_algebra_d Y)
    (hκ : M.mem κ X) (hL : M.mem L X) (hF : M.mem F X)
    (zs : ∀ n m, Rd_entry_d n m z ↔ M.mem n ω ∧ n = m)
    (agree : Er_agree_d I ω X R κ z Γ Y S k)
    (identity : ∀ x y, Rd_entry_d x y k → x = y)
    (family : Em_source_d ω κ L Y F) (component : Ep_component_d I ω κ L Y S F a o) :
    Er_code_d I ω L X R κ F z Y S k a o := by
  obtain ⟨n, D, U, G, p, C, W, hn, fa, space, value, functions, quotient⟩ := component
  have hnx := fs.transitive ω fs.omega_mem n hn
  have ha := (rd_entry_transitive_l fs.transitive hF value).1
  have hu := (rd_entry_transitive_l fs.transitive hF value).2
  obtain ⟨D', hd', ds'⟩ := fs.spaces κ n hκ hn
  have eq := hKP.1.eq_of_same_members D' D (fun s => (ds' s).trans (space s).symm)
  have hd : M.mem D X := eq ▸ hd'
  obtain ⟨D', hDD, _, _⟩ := agree.powers n n D hn ((zs n n).mpr ⟨hn, rfl⟩)
    ((er_space_mem_l I hKP.1 fs mx hκ hn).mpr ⟨hd, space⟩)
  have hDD : Rd_entry_d D D k := (identity D D' hDD).symm ▸ hDD
  have hdY := agree.injection.1.output_mem_of_pairMember hDD
  have points x (hx : M.mem x D) : Rd_entry_d x x k := by
    have hxΓ := agree.downward D x (agree.injection.1.input_mem_of_pairMember hDD)
      (fs.transitive D hd x hx) ((mx.2 x D).mpr ⟨fs.transitive D hd x hx, hd, hx⟩)
    obtain ⟨y, _, hxy⟩ := agree.injection.1.2.2 x hxΓ
    exact (identity x y hxy).symm ▸ hxy
  obtain ⟨i, fi, is⟩ := fn0_identity_l hKP D
  have fiX := fi.mono_target_l (fs.transitive D hd)
  have fiY := fi.mono_target_l (hy D hdY)
  have di : M.IsRestrictionOf I i k D := ⟨(fn0_function_l hKP fi).1.1,
    fun x y => (is x y).trans ⟨fun ⟨hx, eq⟩ => ⟨hx, eq ▸ points x hx⟩,
      fun ⟨hx, hxy⟩ => ⟨hx, identity x y hxy⟩⟩⟩
  have decode {D t f} (ts : ∀ s x, Rd_entry_d s x t ↔ M.mem s D ∧ s = x)
      (hf : M.mem f Y) : Rc_graph_d I Y S t f f := by
    intro s x y hsx
    obtain ⟨_, rfl⟩ := (ts s x).mp hsx
    exact (rf_val_mem_l I hKP.1 hy my hf).symm
  have rawFamily : Rc_family_d I Y S D D i G := by
    intro g
    constructor
    · intro hg
      obtain ⟨hgY, fg⟩ := (functions g).mp hg
      exact ⟨fg, g, (rf_fun_mem_l I hKP.1 hy my hdY).mpr
        (sc_function_domain_l algebra hgY fg), decode is hgY⟩
    · rintro ⟨fg, f, ff, graph⟩
      have sf := (rf_fun_mem_l I hKP.1 hy my hdY).mp ff
      have eq := graph.unique_l I hKP.1 fiY fg (sf.function_l hy) (decode is sf.1)
      exact (functions g).mpr ⟨eq.symm ▸ sf.1, fg⟩
  have base := (family.at_l hKP.1 value fa space).base
  have trace {B} (hB : M.mem B U) : Rt_trace_d I D i R B B := by
    have hb := fs.transitive U hu B hB
    intro s
    constructor
    · intro hs
      have hsD := base.bounds B hB s hs
      exact ⟨hsD, s, (is s s).mpr ⟨hsD, rfl⟩,
        (mx.2 s B).mpr ⟨fs.transitive B hb s hs, hb, hs⟩⟩
    · rintro ⟨_, x, hsx, hxb⟩
      exact ((is s x).mp hsx).2 ▸ ((mx.2 x B).mp hxb).2.2
  refine ⟨n, n, a, D, U, D, i, i, D, U, G, p, C, W, hn, fa,
    (zs n n).mpr ⟨hn, rfl⟩, (rf_fun_mem_l I hKP.1 fs.transitive mx hnx).mpr ⟨ha, L, hL, fa⟩,
    ?_, (er_space_mem_l I hKP.1 fs mx hκ hn).mpr ⟨hd, space⟩,
    (rf_val_mem_l I hKP.1 fs.transitive mx hF).mpr value, ?_, fiX, is, di,
    hDD, ?_, rawFamily, quotient⟩
  · intro s x y hsx
    obtain ⟨_, rfl⟩ := (zs s x).mp hsx
    exact (rf_val_mem_l I hKP.1 fs.transitive mx ha).symm
  · intro x
    exact ⟨fun hx => ⟨fs.transitive D hd x hx, (mx.2 x D).mpr ⟨fs.transitive D hd x hx, hd, hx⟩⟩,
      fun h => ((mx.2 x D).mp h.2).2.2⟩
  · intro A
    constructor
    · intro hA
      have hx := fs.transitive U hu A hA
      exact ⟨A, hx, (mx.2 A U).mpr ⟨hx, hu, hA⟩, trace hA⟩
    · rintro ⟨B, _, hb, tr⟩
      have hB := ((mx.2 B U).mp hb).2.2
      have eq := hKP.1.eq_of_same_members A B (fun s => (tr s).trans (trace hB s).symm)
      exact eq.symm ▸ hB

end Component
end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 实际隶属呈示中的共同图与有限幂一致性

完整前驱方程通过背景成员归纳将共同图逐点识别为恒等。有限幂子集的双向覆盖
随后成为两个真实传递源的子集一致性；不需要共同域等于两源的整个交集。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Er_agree_d.identity_l {ω c X R d Y S κ z Γ k : M.Domain}
    (a : Er_agree_d I ω X R κ z Γ Y S k) (mx : Smem_d I c X R) (my : Smem_d I d Y S)
    (xt : M.TransitiveSet X) (yt : M.TransitiveSet Y) : ∀ x y, Rd_entry_d x y k → x = y := by
  let ρ : Env M 2 := ⟨Fin.cases Γ (fun _ => k),fun _ => Γ⟩
  let φ : UnarySchema 2 := { body := set[3] ⟪⌜(.newest : Term 3)⌝ₛ ∈ ⌜(.bound 1 : Term 3)⌝ₛ →
    ∀ y, ⌜rd_entry0_m⌝ₚ(⌜(.newest : Term 3)⌝ₛ,y,⌜(.bound 2 : Term 3)⌝ₛ) →
      ⌜(.newest : Term 3)⌝ₛ = y⟫ }
  have sat x : φ.denote ρ x ↔ M.mem x Γ → ∀ y, Rd_entry_d x y k → x = y := by
    simp only [φ,UnarySchema.denote,Formula.satisfies_imp_iff,Formula.satisfies_mem_iff,
      Formula.satisfies_forall_iff,rd_entry0_sat_l hZF.1,Formula.satisfies_extensionalEq_iff_eq hZF.1]; rfl
  have all x : φ.denote ρ x := ZF.mem_ind_l M hZF I φ ρ (by
    intro x ih
    apply (sat x).mpr
    intro hx y hxy
    have hxx := a.domain x hx
    have hyy := a.injection.1.output_mem_of_pairMember hxy
    apply hZF.1.eq_of_same_members x y
    intro v
    constructor
    · intro vx
      have rel := (mx.2 v x).mpr ⟨xt x hxx v vx,hxx,vx⟩
      have hv := a.downward x v hx (xt x hxx v vx) rel
      obtain ⟨u,_,hvu⟩ := a.injection.1.2.2 v hv
      have eq := (sat v).mp (ih v vx) hv u hvu
      subst u
      exact ((my.2 v y).mp ((a.predecessors x y hxy v).mpr ⟨v,rel,hvu⟩)).2.2
    · intro vy
      obtain ⟨u,ux,uv⟩ := (a.predecessors x y hxy v).mp
        ((my.2 v y).mpr ⟨yt y hyy v vy,hyy,vy⟩)
      have ux := ((mx.2 u x).mp ux).2.2
      exact (sat u).mp (ih u ux) (a.injection.1.input_mem_of_pairMember uv) v uv ▸ ux) x
  exact fun x y hxy => (sat x).mp (all x) (a.injection.1.input_mem_of_pairMember hxy) y hxy

theorem Er_agree_d.mem_l {ω c X R d Y S κ z Γ k : M.Domain}
    (a : Er_agree_d I ω X R κ z Γ Y S k) (fs : Fs_read_d ω X)
    (mx : Smem_d I c X R) (my : Smem_d I d Y S) (yt : M.TransitiveSet Y)
    (zs : ∀ n m, Rd_entry_d n m z ↔ M.mem n ω ∧ n = m) : Ea_agree_d ω κ X Y := by
  have identity := a.identity_l hZF mx my fs.transitive yt
  have hκ := a.domain κ a.critical
  intro n D A hn space sub
  obtain ⟨D₀,hD₀,ds⟩ := fs.spaces κ n hκ hn
  have eq := hZF.1.eq_of_same_members D₀ D (fun f => (ds f).trans (space f).symm)
  have hD := eq ▸ hD₀
  obtain ⟨E,hDE,left,right⟩ := a.powers n n D hn ((zs n n).mpr ⟨hn,rfl⟩)
    ((er_space_mem_l I hZF.1 fs mx hκ hn).mpr ⟨hD,space⟩)
  have eq := identity D E hDE
  subst E
  have hDY := a.injection.1.output_mem_of_pairMember hDE
  constructor
  · intro hA
    have ha := left A hA (fun x hx hxa =>
      (mx.2 x D).mpr ⟨hx,hD,sub x ((mx.2 x A).mp hxa).2.2⟩)
    obtain ⟨B,hB,hAB⟩ := a.injection.1.2.2 A ha
    exact (identity A B hAB).symm ▸ hB
  · intro hA
    obtain ⟨B,hBA⟩ := right A hA (fun x hx hxa =>
      (my.2 x D).mpr ⟨hx,hDY,sub x ((my.2 x A).mp hxa).2.2⟩)
    exact identity B A hBA ▸ a.domain B (a.injection.1.input_mem_of_pairMember hBA)

end YesMetaZFC.SetTheory.LargeCardinal
