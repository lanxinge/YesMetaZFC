import YesMetaZFC.Model.SetTheory.ReducedPower.RelationCopyPull
import YesMetaZFC.Model.SetTheory.Relations.SeparationSource
import YesMetaZFC.Model.SetTheory.Relations.Ultrafilter
import YesMetaZFC.Model.SetTheory.ReducedPower.SourceModel
import YesMetaZFC.Model.SetTheory.ReducedPower.RelationNormalize
import YesMetaZFC.Model.SetTheory.Source.Transport
import YesMetaZFC.Model.SetTheory.Embedding.RankFixed

/-! # 原关系超幂复制的等值集合与商核

先在原源中分离函数码的等值集合，再搬运同一个集合码。两边实际坐标迹
把集合成员资格读成代表的几乎处处相等；真实测度对应遂给出商核保持。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel FilterZF
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem rc_copy_equalizer_l {ω c a X R Y S π d e f f' g g' : M.Domain}
    (hω : M.IsOmega ω) (mx : Smdl_d I c X R) (my : Smdl_d I a Y S)
    (map : Smap_d I ω c a X Y π) (ext : Rf_ext_d I X R) (theory : Sc_theory_d I ω X R)
    (hd : Rd_entry_d d e π) (hf : Rd_entry_d f f' π) (hg : Rd_entry_d g g' π) :
    ∃ A A', M.mem A X ∧ Rd_entry_d A A' π ∧
      (∀ x, M.mem x X → (Rd_entry_d x A R ↔ Rd_entry_d x d R ∧ ∃ y, M.mem y X ∧
        Rf_val_d I X R x y f ∧ Rf_val_d I X R x y g)) ∧
      (∀ x, M.mem x Y → (Rd_entry_d x A' S ↔ Rd_entry_d x e S ∧ ∃ y, M.mem y Y ∧
        Rf_val_d I Y S x y f' ∧ Rf_val_d I Y S x y g')) := by
  let N := smdl_structure_l I (R := R) mx.2.1
  let P := smdl_structure_l I (R := S) my.2.1
  have ex := ext.native_l I mx.2.1
  have ey₀ : Rf_ext_d I Y S := map.extensional_l hZF hω mx my ext
  have ey := ey₀.native_l I my.2.1
  let D : N.Domain := ⟨d, map.1.1.input_mem_of_pairMember hd⟩
  let E : P.Domain := ⟨e, map.1.1.output_mem_of_pairMember hd⟩
  let F : N.Domain := ⟨f, map.1.1.input_mem_of_pairMember hf⟩
  let G : N.Domain := ⟨g, map.1.1.input_mem_of_pairMember hg⟩
  let F' : P.Domain := ⟨f', map.1.1.output_mem_of_pairMember hf⟩
  let G' : P.Domain := ⟨g', map.1.1.output_mem_of_pairMember hg⟩
  let ψ : UnarySchema 2 := { body := .existsE (.conj
    (rd_entry0_m (.bound 1) .newest (.bound 2)) (rd_entry0_m (.bound 1) .newest (.bound 3))) }
  let ρ : Env N 2 := ⟨Fin.cases F (fun _ => G), fun _ => D⟩
  -- 原源先分离等值集合；随后只搬运这个实际集合码。
  obtain ⟨q, identity, _⟩ := smap_identity_l I hZF (X := X) (c := c) hω
  obtain ⟨A, hA, sep⟩ := sc_separate_raw_l I hZF hω mx theory mx identity ψ ρ D
  obtain ⟨A', hA', hAA⟩ := map.1.1.2.2 A hA
  let B : N.Domain := ⟨A, hA⟩
  let B' : P.Domain := ⟨A', hA'⟩
  let φ : Formula 1 4 := .forallE (.iff (.mem .newest (.bound 3)) (.conj
    (.mem .newest (.bound 4)) (.existsE (.conj
      (rd_entry0_m (.bound 1) .newest (.bound 3)) (rd_entry0_m (.bound 1) .newest (.bound 2))))))
  let η : Env N 4 := ⟨Fin.cases G (Fin.cases F (Fin.cases B (fun _ => D))), fun _ => D⟩
  let θ : Env P 4 := ⟨Fin.cases G' (Fin.cases F' (Fin.cases B' (fun _ => E))), fun _ => E⟩
  have moved := smap_source_l I hZF hω mx my map φ
    (by simp -implicitDefEqProofs [φ, Definitional.Formula.FreeClosed]) η θ
    (Fin.cases hg (Fin.cases hf (Fin.cases hAA (fun _ => hd))))
  simp only [ψ, UnarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, rd_entry0_sat_l ex] at sep
  simp only [φ, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_conj_iff, Formula.satisfies_exists_iff, rd_entry0_sat_l ex, rd_entry0_sat_l ey] at moved
  have next := moved.mp sep
  have read {Z W : M.Domain} (nz : ∃ z, M.mem z Z)
      (ez : Extensional (smdl_structure_l I (R := W) nz))
      (x f g : (smdl_structure_l I (R := W) nz).Domain) :
      (∃ y, Rd_entry_d x y f ∧ Rd_entry_d x y g) ↔ ∃ y, M.mem y Z ∧
        Rf_val_d I Z W x.val y f.val ∧ Rf_val_d I Z W x.val y g.val := by
    exact ⟨fun ⟨y, hf, hg⟩ => ⟨y.val, y.property, (rf_val_native_l I nz ez x y f).mpr hf,
      (rf_val_native_l I nz ez x y g).mpr hg⟩,
      fun ⟨y, hy, hf, hg⟩ => ⟨⟨y, hy⟩, (rf_val_native_l I nz ez x ⟨y, hy⟩ f).mp hf,
        (rf_val_native_l I nz ez x ⟨y, hy⟩ g).mp hg⟩⟩
  exact ⟨A, A', hA, hAA, fun x hx => (sep ⟨x, hx⟩).trans
    (and_congr_right fun _ => read mx.2.1 ex ⟨x, hx⟩ F G),
    fun x hx => (next ⟨x, hx⟩).trans (and_congr_right fun _ => read my.2.1 ey ⟨x, hx⟩ F' G')⟩

/-- 只用滤基及容许迹上的向上封闭，将真实测度对应读成商核保持。 -/
theorem rc_copy_kernel_l {ω c a X R Y S π D E d e t u P Q U V f f' g g' : M.Domain}
    (hω : M.IsOmega ω) (mx : Smdl_d I c X R) (my : Smdl_d I a Y S)
    (map : Smap_d I ω c a X Y π) (ext : Rf_ext_d I X R) (theory : Sc_theory_d I ω X R)
    (hd : Rd_entry_d d e π) (ft : Fn0_d D X t) (fu : Fn0_d E Y u)
    (dt : ∀ s x, Rd_entry_d s x t → Rd_entry_d x d R)
    (du : ∀ s x, Rd_entry_d s x u → Rd_entry_d x e S)
    (hP : Rt_source_d I X R D t P) (hQ : Rt_source_d I Y S E u Q)
    (hU : Base_d D U) (hV : Base_d E V)
    (up : ∀ A B, M.mem A U → M.mem B P → M.MemberSubset A B → M.mem B U)
    (vp : ∀ A B, M.mem A V → M.mem B Q → M.MemberSubset A B → M.mem B V)
    (measure : ∀ A A' B B', M.mem A X →
      (∀ x, M.mem x X → Rd_entry_d x A R → Rd_entry_d x d R) → Rd_entry_d A A' π →
      Rt_trace_d I D t R A B → Rt_trace_d I E u S A' B' → (M.mem B U ↔ M.mem B' V))
    (hf : Rc_copy_d I X R d t Y S u π f f') (hg : Rc_copy_d I X R d t Y S u π g g') :
    Rp_eq_d X U f g ↔ Rp_eq_d Y V f' g' := by
  obtain ⟨F, F', _, gf, hF, gf'⟩ := hf
  obtain ⟨G, G', _, gg, hG, gg'⟩ := hg
  obtain ⟨A, A', hA, hAA, old, next⟩ := rc_copy_equalizer_l hZF hω mx my map ext theory hd hF hG
  obtain ⟨B, tr⟩ := rt_trace_exists_l I hZF D t R A
  obtain ⟨B', tr'⟩ := rt_trace_exists_l I hZF E u S A'
  have hBP := (hP B).mpr ⟨A, hA, tr⟩
  have hBQ := (hQ B').mpr ⟨A', map.1.1.output_mem_of_pairMember hAA, tr'⟩
  -- 两个真实坐标迹由同一对集合码给出，测度对应直接作用于这些迹。
  have copied := measure A A' B B' hA (fun x hx h => ((old x hx).mp h).1) hAA tr tr'
  have read {Z W D t d A B F G f g : M.Domain} (ft : Fn0_d D Z t)
      (dt : ∀ s x, Rd_entry_d s x t → Rd_entry_d x d W) (tr : Rt_trace_d I D t W A B)
      (truth : ∀ x, M.mem x Z → (Rd_entry_d x A W ↔ Rd_entry_d x d W ∧ ∃ y, M.mem y Z ∧
        Rf_val_d I Z W x y F ∧ Rf_val_d I Z W x y G))
      (gf : Rc_graph_d I Z W t F f) (gg : Rc_graph_d I Z W t G g) :
      ∀ s, M.mem s B ↔ M.mem s D ∧ ∃ y, M.mem y Z ∧ Rd_entry_d s y f ∧ Rd_entry_d s y g := by
    intro s
    constructor
    · intro hs
      obtain ⟨hs, x, hsx, hxA⟩ := (tr s).mp hs
      obtain ⟨_, y, hy, hf, hg⟩ := (truth x (ft.bound_l hsx).2).mp hxA
      exact ⟨hs, y, hy, (gf s x y hsx).mpr hf, (gg s x y hsx).mpr hg⟩
    · rintro ⟨hs, y, hy, hf, hg⟩
      obtain ⟨x, hx, hsx⟩ := ft.2.1 s hs
      exact (tr s).mpr ⟨hs, x, hsx, (truth x hx).mpr ⟨dt s x hsx, y, hy,
        (gf s x y hsx).mp hf, (gg s x y hsx).mp hg⟩⟩
  have large {D P U Z f g A : M.Domain} (hU : Base_d D U)
      (up : ∀ A B, M.mem A U → M.mem B P → M.MemberSubset A B → M.mem B U) (hA : M.mem A P)
      (truth : ∀ s, M.mem s A ↔ M.mem s D ∧ ∃ y, M.mem y Z ∧ Rd_entry_d s y f ∧ Rd_entry_d s y g) :
      M.mem A U ↔ Rp_eq_d Z U f g :=
    ⟨fun h => ⟨A, h, fun s hs => ((truth s).mp hs).2⟩, fun ⟨B, hB, h⟩ =>
      up B A hB hA (fun s hs => (truth s).mpr ⟨hU.bounds B hB s hs, h s hs⟩)⟩
  exact (large hU up hBP (read ft dt tr old gf gg)).symm.trans
    (copied.trans (large hV vp hBQ (read fu du tr' next gf' gg')))

/-- 实际生成代表复制图及其商上的单射，不把商核保持作为待证参数。 -/
theorem rc_copy_lift_l {ω c a X R Y S π D E d e t u P Q U V G H p q C N : M.Domain}
    (hω : M.IsOmega ω) (mx : Smdl_d I c X R) (my : Smdl_d I a Y S)
    (map : Smap_d I ω c a X Y π) (ext : Rf_ext_d I X R) (theory : Sc_theory_d I ω X R)
    (hd : Rd_entry_d d e π) (ft : Fn0_d D X t) (fu : Fn0_d E Y u)
    (onto : ∀ x, Rd_entry_d x d R → ∃ s, Rd_entry_d s x t)
    (dt : ∀ s x, Rd_entry_d s x t → Rd_entry_d x d R)
    (du : ∀ s x, Rd_entry_d s x u → Rd_entry_d x e S)
    (source : Rc_family_d I X R D d t G) (target : Rc_family_d I Y S E e u H)
    (hP : Rt_source_d I X R D t P) (hQ : Rt_source_d I Y S E u Q)
    (hU : Base_d D U) (hV : Base_d E V)
    (up : ∀ A B, M.mem A U → M.mem B P → M.MemberSubset A B → M.mem B U)
    (vp : ∀ A B, M.mem A V → M.mem B Q → M.MemberSubset A B → M.mem B V)
    (measure : ∀ A A' B B', M.mem A X →
      (∀ x, M.mem x X → Rd_entry_d x A R → Rd_entry_d x d R) → Rd_entry_d A A' π →
      Rt_trace_d I D t R A B → Rt_trace_d I E u S A' B' → (M.mem B U ↔ M.mem B' V))
    (hp : Rp_map_d I D X U G p C) (hq : Rp_map_d I E Y V H q N) :
    ∃ K j, M.IsSetFunctionFromTo I K G H ∧
      (∀ f g, Rd_entry_d f g K ↔ M.mem f G ∧ M.mem g H ∧ Rc_copy_d I X R d t Y S u π f g) ∧
      M.IsSetInjectionFromTo I j C N ∧ Rp_lift_d I K p q j := by
  obtain ⟨K, hK, spec⟩ := rc_copy_family_l hZF hω mx my map ext hd fu onto du source target
  obtain ⟨j, hj, lift⟩ := rp_lift_exists_l I hZF hU hV hp hq hK (fun f g f' g' hf hg =>
    rc_copy_kernel_l hZF hω mx my map ext theory hd ft fu dt du hP hQ hU hV up vp measure
      ((spec f f').mp hf).2.2 ((spec g g').mp hg).2.2)
  exact ⟨K, j, hK, spec, hj, lift⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 两个原关系超幂之间的完整初等复制

实际坐标覆盖源定义域，因而代表图唯一恢复原函数码。每个内部公式只在其
内部有限支撑上选取商代表；真值集合及其像的测度对应给出完整初等性。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel FilterZF
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 唯一值替换恢复实际代表的函数码，不使用可数选择。 -/
theorem rc_code_map_l {X R D d t G : M.Domain} (nx : ∃ x, M.mem x X)
    (ext : Rf_ext_d I X R) (onto : ∀ x, Rd_entry_d x d R → ∃ s, Rd_entry_d s x t)
    (family : Rc_family_d I X R D d t G) :
    ∃ L, M.IsSetFunctionFromTo I L G X ∧ ∀ g f, Rd_entry_d g f L ↔
      M.mem g G ∧ Rf_fun_d I X R d f ∧ Rc_graph_d I X R t f g := by
  let ρ : Env M 4 := ⟨Fin.cases X (Fin.cases R (Fin.cases d (fun _ => t))), fun _ => X⟩
  let φ : BinarySchema 4 := {
    body := .conj (rf_fun_m (𝒞 := kpair_convention_l) (.bound 2) (.bound 3) (.bound 4) .newest)
      (rc_graph_m (𝒞 := kpair_convention_l) (.bound 2) (.bound 3) (.bound 5) .newest (.bound 1)) }
  have read g f : φ.denote ρ g f ↔ Rf_fun_d I X R d f ∧ Rc_graph_d I X R t f g := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_conj_iff, rf_fun_sat_l I, rc_graph_sat_l I hZF.1]; rfl
  obtain ⟨L, fn, graph⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := G) (target := X)
    (fun g hg => by
      obtain ⟨_, f, ff, code⟩ := (family g).mp hg
      exact ⟨f, (read g f).mpr ⟨ff, code⟩⟩)
    (fun g _ f f' hf hf' => ((read g f).mp hf).2.code_unique_l I nx ext onto
      ((read g f).mp hf).1 ((read g f').mp hf').1 ((read g f').mp hf').2)
    (fun g f _ hf => ((read g f).mp hf).1.mem_l I)
  exact ⟨L, fn, fun g f => (graph g f).trans (and_congr_right fun _ => read g f)⟩

/-- 在真实测度对应下，原关系代表复制直接下降为全部内部公式的初等图。 -/
theorem rc_copy_embedding_l {ω c a X R Y S π D E d e t u P Q U V o₀ o₁ G H p q C N T W : M.Domain}
    (hω : M.IsOmega ω) (mx : Smdl_d I c X R) (my : Smdl_d I a Y S)
    (map : Smap_d I ω c a X Y π) (ext : Rf_ext_d I X R) (theory : Sc_theory_d I ω X R)
    (uniform₀ : Sc_uniform_d I ω X R d) (uniform₁ : Sc_uniform_d I ω Y S e)
    (hd : Rd_entry_d d e π) (ft : Fn0_d D X t) (fu : Fn0_d E Y u)
    (onto : ∀ x, Rd_entry_d x d R → ∃ s, Rd_entry_d s x t)
    (dt : ∀ s x, Rd_entry_d s x t → Rd_entry_d x d R)
    (du : ∀ s x, Rd_entry_d s x u → Rd_entry_d x e S)
    (source : Rc_family_d I X R D d t G) (target : Rc_family_d I Y S E e u H)
    (hP : Rt_source_d I X R D t P) (hQ : Rt_source_d I Y S E u Q)
    (hU : Rel_ultra_d D P U) (hV : Rel_ultra_d E Q V)
    (measure : ∀ A A' B B', M.mem A X →
      (∀ x, M.mem x X → Rd_entry_d x A R → Rd_entry_d x d R) → Rd_entry_d A A' π →
      Rt_trace_d I D t R A B → Rt_trace_d I E u S A' B' → (M.mem B U ↔ M.mem B' V))
    (model₀ : Rp_model_d I D X U R o₀ G p C T) (model₁ : Rp_model_d I E Y V S o₁ H q N W) :
    ∃ K j, M.IsSetFunctionFromTo I K G H ∧
      (∀ f g, Rd_entry_d f g K ↔ M.mem f G ∧ M.mem g H ∧ Rc_copy_d I X R d t Y S u π f g) ∧
      Smap_d I ω o₀ o₁ C N j ∧ Rp_lift_d I K p q j := by
  have ext' : Rf_ext_d I Y S := map.extensional_l hZF hω mx my ext
  have theory' := theory.map_l I hZF hω mx my map
  let d₀ : (smdl_structure_l I (R := R) mx.2.1).Domain := ⟨d, map.1.1.input_mem_of_pairMember hd⟩
  let d₁ : (smdl_structure_l I (R := S) my.2.1).Domain := ⟨e, map.1.1.output_mem_of_pairMember hd⟩
  have family₀ := (rc_family_native_l I mx.2.1 (ext.native_l I mx.2.1) d₀ ft).mp source
  have family₁ := (rc_family_native_l I my.2.1 (ext'.native_l I my.2.1) d₁ fu).mp target
  obtain ⟨K, j, hK, spec, hj, lift⟩ := rc_copy_lift_l hZF hω mx my map ext theory hd ft fu onto dt du
    source target hP hQ hU.base hV.base hU.upward hV.upward measure model₀.map model₁.map
  obtain ⟨L, hL, codes⟩ := rc_code_map_l hZF mx.2.1 ext onto source
  obtain ⟨Z, hZ⟩ := scode_exists_l I hZF hω
  obtain ⟨A₀, hA₀⟩ := ZF.exists_functionSpace hZF I ω X
  obtain ⟨A₁, hA₁⟩ := ZF.exists_functionSpace hZF I ω Y
  obtain ⟨Q₀, hQ₀⟩ := ZF.exists_functionSpace hZF I ω C
  obtain ⟨Q₁, hQ₁⟩ := ZF.exists_functionSpace hZF I ω N
  have context₀ := sc_pe_context_l I mx ext (theory.algebra mx.2.1) d₀.property hA₀
  have context₁ := sc_pe_context_l I my ext' (theory'.algebra my.2.1) d₁.property hA₁
  refine ⟨K, j, hK, spec, ⟨hj, Z, hZ, fun z v₀ v₁ hz hv₀ hv₁ image => ?_⟩, lift⟩
  obtain ⟨n, F, r, code⟩ := (hZ z).mp hz
  obtain ⟨b, hb, bound⟩ := sbound_exists_l I hZF hω code.2.1
  have bω := hω.transitive (ZF.modelsKP hZF) b hb
  -- 只在本公式的内部有限支撑上提升代表；其余坐标由一个实际代表填充。
  obtain ⟨v, hv, finite⟩ := rp_finite_representatives_l I hZF hω hb model₀.map hv₀
  obtain ⟨a₀, ha₀, compose⟩ := ZF.exists_compositionFunction hZF I hv hL
  obtain ⟨a₁, ha₁, assign⟩ := smap_assign_exists_l I hZF map.1.1 ha₀
  have eval₀ : Rc_eval_d I b d X R t p a₀ v₀ := by
    intro i hi
    obtain ⟨g, hg, hig⟩ := hv.2.2 i (bω i hi)
    obtain ⟨f, _, hgf⟩ := hL.2.2 g hg
    obtain ⟨B, _, hgp⟩ := model₀.map.projection.2.2 g hg
    have fn := ((codes g f).mp hgf).2
    exact ⟨f, g, B, (compose i f).mpr ⟨bω i hi, g, hig, hgf⟩,
      fn.1, fn.2, hgp, finite i hi g B hig hgp⟩
  have eval₁ : Rc_eval_d I b e Y S u q a₁ v₁ := by
    intro i hi
    obtain ⟨f, g, B, hif, ff, graph, gp, hiB⟩ := eval₀ i hi
    obtain ⟨g', hg', hgg⟩ := hK.2.2 g (model₀.map.projection.input_mem_of_pairMember gp)
    obtain ⟨f', _, hff⟩ := map.1.1.2.2 f (ff.mem_l I)
    obtain ⟨B', _, gp'⟩ := model₁.map.projection.2.2 g' hg'
    obtain ⟨_, _, v, v', fv, gv, hvv, gv'⟩ := (spec g g').mp hgg
    have eq := graph.code_unique_l I mx.2.1 ext onto ff fv gv
    subst v
    have eq := map.1.1.1.2 f v' f' hvv hff
    subst v'
    exact ⟨f', g', B', assign i (bω i hi) f f' hif hff,
      ff.map_l I hZF hω mx my map hd hff, gv', gp', image i (bω i hi) B B' hiB (lift g g' B B' hgg gp gp')⟩
  -- 原源分离真值对象 B；π(B) 在目标的全部新坐标上仍给出同一公式的真值。
  obtain ⟨B, B', hB, hBB, truth₀, truth₁⟩ := map.pe_trace_l hZF hω context₀ context₁ theory hd
    code.2.1 code.2.2 hb bound ((hA₀ a₀).mpr ha₀) ((hA₁ a₁).mpr ha₁)
    (eval₀.repr_l I ha₀.1) (eval₁.repr_l I ha₁.1) assign
  obtain ⟨A, trace₀⟩ := rt_trace_exists_l I hZF D t R B
  obtain ⟨A', trace₁⟩ := rt_trace_exists_l I hZF E u S B'
  obtain ⟨hAP, read₀⟩ := hP.pointwise_l I (fn0_function_l (ZF.modelsKP hZF) ft) dt hB trace₀ truth₀
  obtain ⟨hAQ, read₁⟩ := hQ.pointwise_l I (fn0_function_l (ZF.modelsKP hZF) fu) du
    (map.1.1.output_mem_of_pairMember hBB) trace₁ truth₁
  have large := measure B B' A A' hB (fun x hx h => ((truth₀ x hx).mp h).1) hBB trace₀ trace₁
  have los₀ := rc_los_l hZF hω mx ext theory d₀ uniform₀ ft dt hP hU family₀ model₀ hA₀ hQ₀
    code.2.1 hb bound code.2.2 a₀ v₀ ((hA₀ a₀).mpr ha₀) ((hQ₀ v₀).mpr hv₀) eval₀
  have los₁ := rc_los_l hZF hω my ext' theory' d₁ uniform₁ fu du hQ hV family₁ model₁ hA₁ hQ₁
    code.2.1 hb bound code.2.2 a₁ v₁ ((hA₁ a₁).mpr ha₁) ((hQ₁ v₁).mpr hv₁) eval₁
  -- 两侧 Łoś 将实际真值迹的测度等价读成商模型中的满足等价。
  exact (satisfies_decode_l I hZF.1 model₀.code code hQ₀).trans (los₀.symm.trans
    ((rc_holds_member_l I hU hAP ft read₀).symm.trans (large.trans
      ((rc_holds_member_l I hV hAQ fu read₁).trans (los₁.trans
        (satisfies_decode_l I hZF.1 model₁.code code hQ₁).symm)))))

end YesMetaZFC.SetTheory.Internal

/-! ## 两个不同源模型的完整超幂复制

函数码沿 π 搬运，再按实际坐标展开代表，得到 [f]↦[π(f)]。两个相对测度只需在源中子集的像上
对应；任意内部公式的真值集合由同一程序搬运，再以两侧 Łoś 证明初等性。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel FilterZF
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem rs_copy_embedding_l {ω c d X R Y S π D D' P Q U V o₀ o₁ G H p₀ p₁ C₀ C₁ T₀ T₁ : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hπ : Smap_d I ω c d X Y π)
    (source : Sc_theory_d I ω X R)
    (u₀ : Sc_uniform_d I ω X R D) (u₁ : Sc_uniform_d I ω Y S D') (hD : M.PairMember I D D' π)
    (hP : Source_d X D P) (hQ : Source_d Y D' Q) (hU : Rel_ultra_d D P U) (hV : Rel_ultra_d D' Q V)
    (measure : ∀ A A', M.mem A P → M.PairMember I A A' π → (M.mem A U ↔ M.mem A' V))
    (hG : ∀ f, M.mem f G ↔ M.mem f X ∧ Fn0_d D X f)
    (hH : ∀ f, M.mem f H ↔ M.mem f Y ∧ Fn0_d D' Y f)
    (hM₀ : Rp_model_d I D X U R o₀ G p₀ C₀ T₀) (hM₁ : Rp_model_d I D' Y V S o₁ H p₁ C₁ T₁) :
    ∃ K j, M.IsSetFunctionFromTo I K G H ∧
      (∀ f g, M.PairMember I f g K ↔ M.mem f G ∧ M.PairMember I f g π) ∧
      Smap_d I ω o₀ o₁ C₀ C₁ j ∧ Rp_lift_d I K p₀ p₁ j := by
  have hDX := hπ.1.1.input_mem_of_pairMember hD
  have hDY := hπ.1.1.output_mem_of_pairMember hD
  have target := source.map_l I hZF hω hm.1 hn.1 hπ
  have sf f (hf : M.mem f G) := sc_function_domain_l (source.algebra_l _ (ZF.modelsKP hZF) hX hm) ((hG f).mp hf).1 ((hG f).mp hf).2
  have sg f (hf : M.mem f H) := sc_function_domain_l (target.algebra_l _ (ZF.modelsKP hZF) hY hn) ((hH f).mp hf).1 ((hH f).mp hf).2
  -- 两个隶属实例用恒等坐标进入同一个原关系代表复制构造。
  obtain ⟨t, ft, ts⟩ := fn0_identity_l (ZF.modelsKP hZF) D
  obtain ⟨u, fu, us⟩ := fn0_identity_l (ZF.modelsKP hZF) D'
  have ftx := ft.mono_target_l (hX D hDX)
  have fuy := fu.mono_target_l (hY D' hDY)
  have decode {c Z W D t f : M.Domain} (tz : M.TransitiveSet Z) (mz : Smem_d I c Z W)
      (ts : ∀ s x, Rd_entry_d s x t ↔ M.mem s D ∧ s = x) (hf : M.mem f Z) : Rc_graph_d I Z W t f f := by
    intro s x y hsx
    obtain ⟨_, rfl⟩ := (ts s x).mp hsx
    exact (rf_val_mem_l I hZF.1 tz mz hf).symm
  have family {c Z W D t G : M.Domain} (tz : M.TransitiveSet Z) (mz : Smem_d I c Z W)
      (hD : M.mem D Z) (ft : Fn0_d D Z t) (ts : ∀ s x, Rd_entry_d s x t ↔ M.mem s D ∧ s = x)
      (fs : ∀ f, M.mem f G ↔ M.mem f Z ∧ Fn0_d D Z f)
      (sf : ∀ f, M.mem f G → Sfun_d Z D f) : Rc_family_d I Z W D D t G := by
    intro g
    constructor
    · intro hg
      exact ⟨((fs g).mp hg).2, g, (rf_fun_mem_l I hZF.1 tz mz hD).mpr (sf g hg), decode tz mz ts ((fs g).mp hg).1⟩
    · rintro ⟨fg, f, ff, graph⟩
      have fn := (rf_fun_mem_l I hZF.1 tz mz hD).mp ff
      have eq := graph.unique_l I hZF.1 ft fg (fn.function_l tz) (decode tz mz ts fn.1)
      exact (fs g).mpr ⟨eq.symm ▸ fn.1, fg⟩
  have trace_read {c Z W D t A B : M.Domain} (tz : M.TransitiveSet Z) (mz : Smem_d I c Z W)
      (ts : ∀ s x, Rd_entry_d s x t ↔ M.mem s D ∧ s = x) (hB : M.mem B Z)
      (tr : Rt_trace_d I D t W B A) : ∀ s, M.mem s A ↔ M.mem s D ∧ M.mem s B := by
    intro s
    refine (tr s).trans ⟨?_, ?_⟩
    · rintro ⟨hs,x,hsx,hx⟩
      obtain ⟨_,rfl⟩ := (ts s x).mp hsx
      exact ⟨hs,((mz.2 s B).mp hx).2.2⟩
    · rintro ⟨hs,hb⟩
      exact ⟨hs,s,(ts s s).mpr ⟨hs,rfl⟩,(mz.2 s B).mpr ⟨tz B hB s hb,hB,hb⟩⟩
  -- 任意源集合的坐标迹是它与定义域的交，因此仍属于原容许子集代数。
  have admissible {c Z W D t P : M.Domain} (tz : M.TransitiveSet Z) (mz : Smem_d I c Z W)
      (theory : Sc_theory_d I ω Z W) (hD : M.mem D Z)
      (ts : ∀ s x, Rd_entry_d s x t ↔ M.mem s D ∧ s = x) (hp : Source_d Z D P) : Rt_source_d I Z W D t P := by
    intro A
    constructor
    · intro hA
      obtain ⟨ha,sub⟩ := (hp A).mp hA
      refine ⟨A,ha,fun s => ?_⟩
      constructor
      · intro hs
        exact ⟨sub s hs,s,(ts s s).mpr ⟨sub s hs,rfl⟩,(mz.2 s A).mpr ⟨tz A ha s hs,ha,hs⟩⟩
      · rintro ⟨_,x,hsx,hx⟩
        obtain ⟨_,rfl⟩ := (ts s x).mp hsx
        exact ((mz.2 s A).mp hx).2.2
    · rintro ⟨B,hB,tr⟩
      let φ : UnarySchema 1 := { body := .mem .newest (.bound 1) }
      let ρ : Env M 1 := ⟨fun _ => B,fun _ => B⟩
      obtain ⟨C,hC,cs⟩ := sc_separate_source_l I hZF hω tz mz theory φ (.mem _ _) ρ (fun _ => hB) hD
      have eq : A = C := hZF.1.eq_of_same_members A C (fun s => (trace_read tz mz ts hB tr s).trans
        (show M.mem s C ↔ M.mem s D ∧ M.mem s B from cs s).symm)
      exact (hp A).mpr ⟨eq.symm ▸ hC,fun s hs => ((tr s).mp hs).1⟩
  -- 在这个隶属实例中，规范化子集的实际迹就是该子集本身。
  have transport A A' B B' (hA : M.mem A X)
      (sub : ∀ x, M.mem x X → Rd_entry_d x A R → Rd_entry_d x D R) (hAA : Rd_entry_d A A' π)
      (tr : Rt_trace_d I D t R A B) (tr' : Rt_trace_d I D' u S A' B') : M.mem B U ↔ M.mem B' V := by
    have sa : M.MemberSubset A D := fun x hx => ((hm.2 x D).mp
      (sub x (hX A hA x hx) ((hm.2 x A).mpr ⟨hX A hA x hx,hA,hx⟩))).2.2
    have sb := (hπ.subset_l hZF hω hX hY hm hn hAA hD).mp sa
    have eq : B = A := hZF.1.eq_of_same_members B A (fun s => (trace_read hX hm ts hA tr s).trans
      ⟨And.right,fun hs => ⟨sa s hs,hs⟩⟩)
    have eq' : B' = A' := hZF.1.eq_of_same_members B' A' (fun s =>
      (trace_read hY hn us (hπ.1.1.output_mem_of_pairMember hAA) tr' s).trans ⟨And.right,fun hs => ⟨sb s hs,hs⟩⟩)
    subst B B'
    exact measure A A' ((hP A).mpr ⟨hA,sa⟩) hAA
  obtain ⟨K,j,hK,raw,hj,lift⟩ := rc_copy_embedding_l hZF hω hm.1 hn.1 hπ
    (rf_ext_mem_l I hZF.1 hX hm) source u₀ u₁ hD ftx fuy
    (fun x hx => ⟨x,(ts x x).mpr ⟨((hm.2 x D).mp hx).2.2,rfl⟩⟩)
    (fun s x hsx => by
      obtain ⟨hs,rfl⟩ := (ts s x).mp hsx
      exact (hm.2 s D).mpr ⟨hX D hDX s hs,hDX,hs⟩)
    (fun s x hsx => by
      obtain ⟨hs,rfl⟩ := (us s x).mp hsx
      exact (hn.2 s D').mpr ⟨hY D' hDY s hs,hDY,hs⟩)
    (family hX hm hDX ftx ts hG sf) (family hY hn hDY fuy us hH sg)
    (admissible hX hm source hDX ts hP) (admissible hY hn target hDY us hQ)
    hU hV transport hM₀ hM₁
  have ks f g : M.PairMember I f g K ↔ M.mem f G ∧ M.PairMember I f g π := by
    constructor
    · intro hfg
      obtain ⟨hf, hg, v, v', fv, graph, hvv, graph'⟩ := (raw f g).mp hfg
      have fn := (rf_fun_mem_l I hZF.1 hX hm hDX).mp fv
      have eq := graph.unique_l I hZF.1 ftx ((hG f).mp hf).2 (fn.function_l hX) (decode hX hm ts fn.1)
      subst v
      have fv' := (rf_fun_mem_l I hZF.1 hY hn hDY).mp (fv.map_l I hZF hω hm.1 hn.1 hπ hD hvv)
      have eq := graph'.unique_l I hZF.1 fuy ((hH g).mp hg).2 (fv'.function_l hY) (decode hY hn us fv'.1)
      exact ⟨hf, eq.symm ▸ hvv⟩
    · rintro ⟨hf, hfg⟩
      have fn := hπ.sfun_l hZF hω hX hY hm hn hD hfg (sf f hf)
      exact (raw f g).mpr ⟨hf, (hH g).mpr ⟨fn.1, fn.function_l hY⟩, f, g,
        (rf_fun_mem_l I hZF.1 hX hm hDX).mpr (sf f hf), decode hX hm ts ((hG f).mp hf).1,
        hfg, decode hY hn us fn.1⟩
  exact ⟨K, j, hK, ks, hj, lift⟩

end YesMetaZFC.SetTheory.Internal
