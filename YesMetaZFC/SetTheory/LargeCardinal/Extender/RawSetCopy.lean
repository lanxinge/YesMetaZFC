import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawCopy
import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawCopyPull
import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawCopySyntax
import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawGraphSyntax
import YesMetaZFC.Model.SetTheory.DirectedSystem.ElementaryFactor
import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawAgreementRead
import YesMetaZFC.SetTheory.LargeCardinal.Extender.TupleValue
import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawPresent
import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawCopyEvaluation
import YesMetaZFC.Model.SetTheory.Relations.LayerComposition
import YesMetaZFC.Model.SetTheory.Relations.RecordImage
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.AttemptMember
import YesMetaZFC.Model.SetTheory.Embedding.Theory
import YesMetaZFC.Model.SetTheory.Relations.Hierarchy
import YesMetaZFC.SetTheory.CumulativeComparison
import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawEvaluationRead
import YesMetaZFC.SetTheory.LargeCardinal.Extender.BoundedValue
import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawOwnedCopy
import YesMetaZFC.SetTheory.LargeCardinal.Extender.SetInclusion
import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawMembershipSystem

/-! # 原关系商类复制保持实际系统箭头

源箭头作用于类中的实际代表。分量复制给出目标代表，坐标投影的复制
相容性再把同一个拉回方程送入目标系统。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 两端分量与支撑投影的完整对象码载体一致。 -/
theorem Er_coord_d.frame_domains_l
    {ω L N T w F z X R k a b o₀ o₁ n m f d u D i t y V G p C W
      n' m' f' d' u' E i' t' y' V' G' p' C' W' D₁ E₁ s : M.Domain}
    (numbers : Rr_layer_d I ω N T w z)
    (ext : Extensional (smdl_structure_l I (R := T) ⟨w, numbers.member⟩))
    (ξ ℓ : (smdl_structure_l I (R := T) ⟨w, numbers.member⟩).Domain)
    (length : ∀ x, M.mem x L ↔ M.mem x N ∧ Rd_entry_d x ℓ.val T)
    (first : Er_frame_d I ω L N T ξ.val F z X R k a o₀ n m f d u D i t y V G p C W)
    (last : Er_frame_d I ω L N T ξ.val F z X R k b o₁ n' m' f' d' u' E i' t' y' V' G' p' C' W')
    (coord : Er_coord_d I ω L N T ξ.val ℓ.val z a b D₁ E₁ s) : D₁ = D ∧ E₁ = E := by
  let nx := (⟨w, numbers.member⟩ : ∃ x, M.mem x N)
  obtain ⟨hn, fa, hnm, fn, ga, space, _, dc, _⟩ := first
  obtain ⟨hn', fb, hnm', fn', gb, space', _, ec, _⟩ := last
  let m₀ : (smdl_structure_l I (R := T) nx).Domain := ⟨m, numbers.injection.1.output_mem_of_pairMember hnm⟩
  let m₁ : (smdl_structure_l I (R := T) nx).Domain := ⟨m', numbers.injection.1.output_mem_of_pairMember hnm'⟩
  let f₀ : (smdl_structure_l I (R := T) nx).Domain := ⟨f, fn.mem_l I⟩
  let f₁ : (smdl_structure_l I (R := T) nx).Domain := ⟨f', fn'.mem_l I⟩
  let d₀ : (smdl_structure_l I (R := T) nx).Domain := ⟨d, space.elim fun h _ => h 0⟩
  let d₁ : (smdl_structure_l I (R := T) nx).Domain := ⟨d', space'.elim fun h _ => h 0⟩
  have fa₀ := numbers.function_range_l hZF ext m₀ ℓ f₀ hnm fa (fun x hx => ((length x).mp hx).2) fn ga
  have fb₀ := numbers.function_range_l hZF ext m₁ ℓ f₁ hnm' fb (fun x hx => ((length x).mp hx).2) fn' gb
  obtain ⟨dc₁, ec₁, _⟩ := coord.native_l hZF numbers ext ξ ℓ m₀ m₁ f₀ f₁ d₀ d₁
    ⟨n, m, hn, fa, hnm, fn, ga⟩ ⟨n', m', hn', fb, hnm', fn', gb⟩ fa₀ fb₀
    ((er_space_native_l I nx ext ξ m₀ d₀).mp space) ((er_space_native_l I nx ext ξ m₁ d₁).mp space')
  exact ⟨hZF.1.eq_of_same_members D₁ D (fun x => (dc₁ x).trans (dc x).symm),
    hZF.1.eq_of_same_members E₁ E (fun x => (ec₁ x).trans (ec x).symm)⟩

/-- 实际类复制保持整张系统的边；中间代表由原边提升，不选择规范代表。 -/
theorem Er_graph_d.copy_arrow_l
    {ω c N T c' N' T' σ h X R h' Y S π Γ Γ' k k' z z' L L'
      J O Z A p V W J' O' Z' A' p' V' W' u v u' v' a b a' b' B C B' C' : M.Domain}
    (hω : M.IsOmega ω) (mx : Smdl_d I c N T) (my : Smdl_d I c' N' T')
    (map : Smap_d I ω c c' N N' σ)
    (hN : (smdl_structure_l I (R := T) mx.2.1).Models KP)
    (hN' : (smdl_structure_l I (R := T') my.2.1).Models KP)
    (w ξ ℓ f : (smdl_structure_l I (R := T) mx.2.1).Domain)
    (w' ξ' ℓ' f' : (smdl_structure_l I (R := T') my.2.1).Domain)
    (hξ : Rd_entry_d ξ.val ξ'.val σ)
    (hℓ : Rd_entry_d ℓ.val ℓ'.val σ) (hf : Rd_entry_d f.val f'.val σ)
    (numbers : Rr_layer_d I ω N T w.val z) (numbers' : Rr_layer_d I ω N' T' w'.val z')
    (length : ∀ x, M.mem x L ↔ M.mem x N ∧ Rd_entry_d x ℓ.val T)
    (length' : ∀ x, M.mem x L' ↔ M.mem x N' ∧ Rd_entry_d x ℓ'.val T')
    (loc : It_local_d I w.val N T ξ.val ℓ.val f.val)
    (powers : ∀ m d : (smdl_structure_l I (R := T) mx.2.1).Domain,
      (smdl_structure_l I (R := T) mx.2.1).mem m w → Ep_space_d ξ m d →
        ∃ p, (smdl_structure_l I (R := T) mx.2.1).IsPowerSetOf p d)
    (parent : Smdl_d I h X R) (parent' : Smdl_d I h' Y S) (copy : Smap_d I ω h h' X Y π)
    (px : Rf_ext_d I X R) (theory : Sc_theory_d I ω X R) (collection : Sc_collection_d I ω X R)
    (agree : Er_agree_d I ω N T ξ.val z Γ X R k)
    (agree' : Er_agree_d I ω N' T' ξ'.val z' Γ' Y S k')
    (maps : Er_maps_d I ω N T ξ.val z k k' π σ)
    (small : ∀ n m d y, M.mem n ω → Rd_entry_d n m z → Er_space_d I N T ξ.val m d →
      Rd_entry_d d y k → Rf_small_d I X R y)
    (source : Er_graph_d I ω L N T ξ.val ℓ.val f.val z X R k J O Z A p V W)
    (target : Er_graph_d I ω L' N' T' ξ'.val ℓ'.val f'.val z' Y S k' J' O' Z' A' p' V' W')
    (hu : KPair_d M u a B) (hv : KPair_d M v b C) (edge : Rd_entry_d u v V)
    (hu' : KPair_d M u' a' B') (hv' : KPair_d M v' b' C') (huA : M.mem u' A') (hvA : M.mem v' A')
    (first : Er_class_d I ω L N T ξ.val f.val z X R k L' N' T' ξ'.val f'.val z' Y S k' π σ a a' B B')
    (last : Er_class_d I ω L N T ξ.val f.val z X R k L' N' T' ξ'.val f'.val z' Y S k' π σ b b' C C') :
    Rd_entry_d u' v' V' := by
  have ext : Rf_ext_d I N T := fun x hx y hy same => congrArg Subtype.val
    (hN.1.eq_of_same_members ⟨x, hx⟩ ⟨y, hy⟩ (fun z => same z.val z.property))
  have ext' : Rf_ext_d I N' T' := map.extensional_l hZF hω mx my ext
  have ex := ext.native_l I mx.2.1
  have ey := ext'.native_l I my.2.1
  have inside x hx := ((length x).mp hx).1
  have inside' x hx := ((length' x).mp hx).1
  have hab := ((source.arrow_l hu hv).mp edge).2.2.1
  have ab := (source.order_spec a b).mp hab
  have ha' := (target.indices a').mpr (first.support_l hZF inside map.1 ((source.indices a).mp ab.1))
  have hb' := (target.indices b').mpr (last.support_l hZF inside map.1 ((source.indices b).mp ab.2.1))
  have last₀ := last
  -- 起点类提供一对实际复制代表；终点分量的复制允许搬运任意到达代表。
  obtain ⟨oA, oA', nA, mA, fA, dA, uA, DA, iA, tA, yA, VA, GA, pA, CA, WA,
    mA', fA', dA', uA', DA', iA', tA', yA', VA', GA', pA', CA', WA',
    frameA, frameA', aa, hB, hB', g, g', hg, hg', cg⟩ := first
  obtain ⟨oB, oB', nB, mB, fB, dB, uB, EB, iB, tB₀, yB₀, VB, GB, pB₀, CB, WB,
    mB', fB', dB', uB', EB', iB', tB₀', yB₀', VB', GB', pB₀', CB', WB',
    frameB₀, frameB₀', bb, _⟩ := last
  have fa := frameA.2.1
  have fa' := frameA'.2.1
  have fb := frameB₀.2.1
  have fb' := frameB₀'.2.1
  have codeB : Er_code_d I ω L N T ξ.val f.val z X R k b oB :=
    ⟨nB, mB, fB, dB, uB, EB, iB, tB₀, yB₀, VB, GB, pB₀, CB, WB, frameB₀⟩
  have codeB' : Er_code_d I ω L' N' T' ξ'.val f'.val z' Y S k' b' oB' :=
    ⟨nB, mB', fB', dB', uB', EB', iB', tB₀', yB₀', VB', GB', pB₀', CB', WB', frameB₀'⟩
  obtain ⟨DB, DB', tB, tB', yB, yB', UB, UB', HB, HB', pB, pB', MB, MB', SB, SB', K, jB, _, _,
    ftB, ftB', _, dataB, dataB', _, _, embB, _, _, classB, anyB, _⟩ :=
    codeB.copy_l hZF hω mx my map hN hN' w ξ ℓ f w' ξ' ℓ' f' hξ hℓ hf numbers numbers' length length'
      loc powers parent parent' copy px theory collection agree agree' maps small fb fb' bb codeB'
  have hCC := (classB C C').mpr last₀
  obtain ⟨D₂, E₂, s, h₀, coord, hh, pull⟩ := source.lift_l hZF.1 hu hv edge hg
  obtain ⟨h₁, hh', ch⟩ := anyB C C' hCC h₀ hh
  obtain ⟨_, _, _, _, _, _, _, D₂', E₂', s', edge', _, _, _, _, _, _, coord', _⟩ :=
    source.copy_coordinates_l hZF hω mx my map ext w ξ ℓ w' ξ' ℓ' hξ hℓ numbers numbers'
      inside inside' target fa fa' aa fb fb' bb ha' hb' hab coord
  obtain ⟨n₂, m₂, f₂, d₂, u₂, i₂, frameB⟩ := dataB
  obtain ⟨n₂', m₂', f₂', d₂', u₂', i₂', frameB'⟩ := dataB'
  -- 两个投影均识别到同一分量的完整坐标载体，随后使用原代表的交换方程。
  have ⟨eqD, eqE⟩ := coord.frame_domains_l hZF numbers ex ξ ℓ length frameA frameB
  have ⟨eqD', eqE'⟩ := coord'.frame_domains_l hZF numbers' ey ξ' ℓ' length' frameA' frameB'
  subst D₂ E₂ D₂' E₂'
  obtain ⟨_, _, _, _, _, spA, _, dcA, _, _, rtA, hdA, _, _, modelA⟩ := frameA
  obtain ⟨_, _, _, _, _, spA', _, dcA', _, _, rtA', hdA', _, _, modelA'⟩ := frameA'
  obtain ⟨_, _, _, _, _, spB, _, dcB, _, _, rtB, hdB, _, _, _⟩ := frameB
  obtain ⟨_, _, _, _, _, spB', _, dcB', _, _, rtB', hdB', _, _, modelB'⟩ := frameB'
  have ftA := fn0_of_function_l (ZF.modelsKP hZF) (rtA.isSetFunctionFromTo agree.injection.1
    (fun x hx => agree.downward dA x (agree.injection.1.input_mem_of_pairMember hdA) ((dcA x).mp hx).1 ((dcA x).mp hx).2))
  have ftA' := fn0_of_function_l (ZF.modelsKP hZF) (rtA'.isSetFunctionFromTo agree'.injection.1
    (fun x hx => agree'.downward dA' x (agree'.injection.1.input_mem_of_pairMember hdA') ((dcA' x).mp hx).1 ((dcA' x).mp hx).2))
  have fg := modelA.map.functions g (modelA.map.member_family_l I hB hg)
  have fg' := modelA'.map.functions g' (modelA'.map.member_family_l I hB' hg')
  have fh' := modelB'.map.functions h₁ (modelB'.map.member_family_l I (embB.1.1.output_mem_of_pairMember hCC) hh')
  let da : (smdl_structure_l I (R := T) mx.2.1).Domain := ⟨dA, spA.elim fun h _ => h 0⟩
  let db : (smdl_structure_l I (R := T) mx.2.1).Domain := ⟨d₂, spB.elim fun h _ => h 0⟩
  let da' : (smdl_structure_l I (R := T') my.2.1).Domain := ⟨dA', spA'.elim fun h _ => h 0⟩
  let db' : (smdl_structure_l I (R := T') my.2.1).Domain := ⟨d₂', spB'.elim fun h _ => h 0⟩
  have actual := loc.read_l I mx.2.1 (kp_pair_l hN) ex w ξ ℓ f
  obtain ⟨_, _, _, injb'⟩ := (target.indices b').mp hb'
  have pull' := coord.copy_pull_l hZF hω mx my map ext w ξ ℓ da db w' ξ' ℓ' da' db'
    (fun r => KP.exists_pair hN r r) actual.critical.1.transitive actual.uncountable hξ hℓ
    numbers numbers' fa fa' aa fb fb' bb inside' injb'
    parent parent' copy px agree agree' maps hdA hdB hdA' hdB' dcA dcB dcA' dcB'
    ftA ftB ftA' ftB' rtA rtB rtA' rtB' coord' fg fg' fh' cg ch pull
  exact (target.arrow_l hu' hv').mpr ⟨huA, hvA, edge', DA', DB', s', g', h₁, coord', fg', hg', hh', pull'⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 两个原关系有限支撑极限之间的完整复制

分量复制先进入目标极限；统一节点公式经唯一值替换形成实际节点函数。
系统边的复制保持给出交换律，实际初等锥唯一下降到原极限，并保持父模型常值方块。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Er_graph_d.copy_limit_l
    {ω c N T c' N' T' σ h X R h' Y S π Γ Γ' k k' z z' L L'
      J O Z A p V W J' O' Z' A' p' V' W' q o C U q' o' C' U' : M.Domain}
    (hω : M.IsOmega ω) (mx : Smdl_d I c N T) (my : Smdl_d I c' N' T')
    (map : Smap_d I ω c c' N N' σ)
    (hN : (smdl_structure_l I (R := T) mx.2.1).Models KP)
    (hN' : (smdl_structure_l I (R := T') my.2.1).Models KP)
    (w ξ ℓ f : (smdl_structure_l I (R := T) mx.2.1).Domain)
    (w' ξ' ℓ' f' : (smdl_structure_l I (R := T') my.2.1).Domain)
    (hξ : Rd_entry_d ξ.val ξ'.val σ)
    (hℓ : Rd_entry_d ℓ.val ℓ'.val σ) (hf : Rd_entry_d f.val f'.val σ)
    (numbers : Rr_layer_d I ω N T w.val z) (numbers' : Rr_layer_d I ω N' T' w'.val z')
    (length : ∀ x, M.mem x L ↔ M.mem x N ∧ Rd_entry_d x ℓ.val T)
    (length' : ∀ x, M.mem x L' ↔ M.mem x N' ∧ Rd_entry_d x ℓ'.val T')
    (loc : It_local_d I w.val N T ξ.val ℓ.val f.val)
    (powers : ∀ m d : (smdl_structure_l I (R := T) mx.2.1).Domain,
      (smdl_structure_l I (R := T) mx.2.1).mem m w → Ep_space_d ξ m d →
        ∃ p, (smdl_structure_l I (R := T) mx.2.1).IsPowerSetOf p d)
    (parent : Smdl_d I h X R) (parent' : Smdl_d I h' Y S) (copy : Smap_d I ω h h' X Y π)
    (px : Rf_ext_d I X R) (theory : Sc_theory_d I ω X R) (collection : Sc_collection_d I ω X R)
    (agree : Er_agree_d I ω N T ξ.val z Γ X R k)
    (agree' : Er_agree_d I ω N' T' ξ'.val z' Γ' Y S k')
    (maps : Er_maps_d I ω N T ξ.val z k k' π σ)
    (small : ∀ n m d y, M.mem n ω → Rd_entry_d n m z → Er_space_d I N T ξ.val m d →
      Rd_entry_d d y k → Rf_small_d I X R y)
    (source : Er_graph_d I ω L N T ξ.val ℓ.val f.val z X R k J O Z A p V W)
    (target : Er_graph_d I ω L' N' T' ξ'.val ℓ'.val f'.val z' Y S k' J' O' Z' A' p' V' W')
    (diagram : Di_system_d J O A p V W) (diagram' : Di_system_d J' O' A' p' V' W')
    (limit : Di_limit_d A p V W q C U) (model : Smdl_d I o C U)
    (limit' : Di_limit_d A' p' V' W' q' C' U') (model' : Smdl_d I o' C' U') :
    Er_limit_d hZF ω L N T ξ.val f.val z X R k L' N' T' ξ'.val f'.val z' Y S k' π σ q q' h h' o C U o' C' U' := by
  have ext : Rf_ext_d I N T := fun x hx y hy same => congrArg Subtype.val
    (hN.1.eq_of_same_members ⟨x, hx⟩ ⟨y, hy⟩ (fun z => same z.val z.property))
  have hw := (numbers.omega_map_l I hZF hω mx my map ext
    (map.extensional_l hZF hω mx my ext) numbers').1
  obtain ⟨_, table⟩ := source.codes
  have inside x hx := ((length x).mp hx).1
  have component a a' n o₀ o₁ (fa : Fn0_d n L a) (fa' : Fn0_d n L' a') (assign : Smap_assign_d I n σ a a')
      (code : Er_code_d I ω L N T ξ.val f.val z X R k a o₀)
      (code' : Er_code_d I ω L' N' T' ξ'.val f'.val z' Y S k' a' o₁) :=
    code.copy_l hZF hω mx my map hN hN' w ξ ℓ f w' ξ' ℓ' f' hξ hℓ hf numbers numbers' length length'
      loc powers parent parent' copy px theory collection agree agree' maps small fa fa' assign code'
  -- 每个源分量先复制到实际目标支撑，再进入同一个目标原关系极限。
  have into a b (hab : Rd_entry_d a b Z) : ∃ D S₀ t, Smdl_d I b D S₀ ∧ Smap_d I ω b o' D C' t ∧
      ∀ u B E, KPair_d M u a B → (Rd_entry_d B E t ↔ M.mem B D ∧
        Er_node_d I ω L N T ξ.val f.val z X R k L' N' T' ξ'.val f'.val z' Y S k' π σ q' u E) := by
    obtain ⟨n, a', b₀, b', _, fa, fa', assign, _, _, hab₀, hab', code, code'⟩ :=
      source.copy_index_l hZF hω mx my map hℓ length length' target (table.bound_l hab).1
    have eq := (fn0_function_l (ZF.modelsKP hZF) table).1.2 a b₀ b hab₀ hab
    subst b₀
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, D, D', S₀, S₁, _, j, _, _,
      _, _, _, data, data', _, _, embed, _, _, classes, _⟩ := component a a' n b b' fa fa' assign code code'
    have m₀ : Smdl_d I b D S₀ := by
      obtain ⟨_, _, _, _, _, _, frame⟩ := data
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, quotient⟩ := frame
      exact quotient.code
    have m₁ : Smdl_d I b' D' S₁ := by
      obtain ⟨_, _, _, _, _, _, frame⟩ := data'
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, quotient⟩ := frame
      exact quotient.code
    obtain ⟨s, hs, ss⟩ := target.stage_l hZF hω diagram' limit' model' hab' m₁
    obtain ⟨t, ht, ts⟩ := smap_comp_l I hZF embed hs
    refine ⟨D, S₀, t, m₀, ht, fun u B E hu => (ts B E).trans (and_congr_right fun hB => ?_)⟩
    constructor
    · rintro ⟨B', hBB, hBE⟩
      obtain ⟨_, v, hv, hvE⟩ := (ss B' E).mp hBE
      exact ⟨a, B, a', B', v, hu, (classes B B').mp hBB, hv, hvE⟩
    · rintro ⟨a₀, B₀, a₁, B', v, hu₀, copied, hv, hvE⟩
      obtain ⟨rfl, rfl⟩ := kpair_injective_l M hu hu₀
      have eq := copied.support_eq_l hZF inside map.1.1 fa fa' assign
      subst a₁
      have hBB := (classes B B').mpr copied
      exact ⟨B', hBB, (ss B' E).mpr ⟨embed.1.1.output_mem_of_pairMember hBB, v, hv, hvE⟩⟩
  have atMap u (hu : M.mem u A) : ∃ a B b D t, KPair_d M u a B ∧ M.mem B D ∧ Smap_d I ω b o' D C' t ∧
      ∀ E, Rd_entry_d B E t ↔ Er_node_d I ω L N T ξ.val f.val z X R k L' N' T' ξ'.val f'.val z' Y S k' π σ q' u E := by
    obtain ⟨a, B, pair, b, D₀, S₀, hab, code, hB⟩ := (source.nodes u).mp hu
    obtain ⟨D, S₁, t, m₀, ht, ts⟩ := into a b hab
    obtain ⟨rfl, rfl⟩ := kpair_injective_l M m₀.1 code
    exact ⟨a, B, b, D, t, pair, hB, ht, fun E => (ts u B E pair).trans (and_iff_right hB)⟩
  -- 唯一值替换形成实际节点函数，参数只包含原模型、坐标和两张给定图。
  let ρ : Env M 22 := ⟨fun i =>
    [ω, L, N, T, ξ.val, f.val, z, X, R, k, L', N', T', ξ'.val, f'.val, z', Y, S, k', π, σ, q'].get i,
    fun _ => ω⟩
  let φ : BinarySchema 22 := {
    body := er_node_m (.bound 2) (.bound 3) (.bound 4) (.bound 5) (.bound 6)
      (.bound 7) (.bound 8) (.bound 9) (.bound 10) (.bound 11) (.bound 12) (.bound 13) (.bound 14)
      (.bound 15) (.bound 16) (.bound 17) (.bound 18) (.bound 19) (.bound 20) (.bound 21) (.bound 22)
      (.bound 23) (.bound 1) .newest }
  have sat u E : φ.denote ρ u E ↔
      Er_node_d I ω L N T ξ.val f.val z X R k L' N' T' ξ'.val f'.val z' Y S k' π σ q' u E := by
    simp only [φ, BinarySchema.denote, er_node_sat_l I hZF.1]; rfl
  obtain ⟨Q, fQ, qs⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := A) (target := C')
    (fun u hu => by
      obtain ⟨_, B, _, _, t, _, hB, ht, ts⟩ := atMap u hu
      obtain ⟨E, _, hBE⟩ := ht.1.1.2.2 B hB
      exact ⟨E, (sat u E).mpr ((ts E).mp hBE)⟩)
    (fun u hu E H he hh => by
      obtain ⟨_, B, _, _, _, _, _, ht, ts⟩ := atMap u hu
      exact ht.1.1.1.2 B E H ((ts E).mpr ((sat u E).mp he)) ((ts H).mpr ((sat u H).mp hh)))
    (fun u E hu he => by
      obtain ⟨_, _, _, _, _, _, _, ht, ts⟩ := atMap u hu
      exact ht.1.1.output_mem_of_pairMember ((ts E).mpr ((sat u E).mp he)))
  have spec u E := (qs u E).trans (and_congr_right fun _ => sat u E)
  have comm u v E H (huv : Rd_entry_d u v V) (huE : Rd_entry_d u E Q) (hvH : Rd_entry_d v H Q) : E = H := by
    obtain ⟨a, B, a', B', u', hu, first, hu', hu'E⟩ := ((spec u E).mp huE).2
    obtain ⟨b, C₀, b', C₁, v', hv, last, hv', hv'H⟩ := ((spec v H).mp hvH).2
    have edge := source.copy_arrow_l hZF hω mx my map hN hN' w ξ ℓ f w' ξ' ℓ' f'
      hξ hℓ hf numbers numbers' length length' loc powers parent parent' copy px theory collection agree agree' maps small
      target hu hv huv hu' hv' (limit'.projection.bound_l hu'E).1 (limit'.projection.bound_l hv'H).1 first last
    exact limit'.commute_l diagram' edge hu'E hv'H
  -- 每个标签分量的锥直接由去标签同构和已构造的原分量映射组成。
  have cone a b D S₀ (stage : Di_stage_d I A p W a b D S₀) : ∃ t, Smap_d I ω b o' D C' t ∧
      ∀ u E, Rd_entry_d u E t ↔ M.mem u D ∧ Rd_entry_d u E Q := by
    obtain ⟨u, hu⟩ := stage.1.2.1
    obtain ⟨b₀, _, hab⟩ := table.2.1 a (source.projection.bound_l ((stage.2.1 u).mp hu).2).2
    obtain ⟨D₀, S₁, s, m₀, hs, ss⟩ := into a b₀ hab
    obtain ⟨t, _, ht, _, ts, _⟩ := ep_tag_l hZF hω source.codes source.nodes source.index source.label_l source.relation_l stage hab m₀
    obtain ⟨r, hr, rs⟩ := smap_comp_l I hZF ht hs
    refine ⟨r, hr, fun u E => (rs u E).trans (and_congr_right fun hu => ?_)⟩
    constructor
    · rintro ⟨B, huB, hBE⟩
      exact (spec u E).mpr ⟨((stage.2.1 u).mp hu).1, ((ss u B E ((ts u B).mp huB).2).mp hBE).2⟩
    · intro huE
      obtain ⟨B, hB, huB⟩ := ht.1.1.2.2 u hu
      exact ⟨B, huB, (ss u B E ((ts u B).mp huB).2).mpr ⟨hB, ((spec u E).mp huE).2⟩⟩
  obtain ⟨τ, hτ, law, unique⟩ := di_factor_elementary_l hZF hω diagram limit (source.elementary_l hZF hω)
    model model' (fn0_of_function_l (ZF.modelsKP hZF) fQ) comm cone
  -- 选取一个实际分量，将其两条常值嵌入接入同一对原极限。
  obtain ⟨B₀, hB₀⟩ := model.2.1
  obtain ⟨u₀, hu₀⟩ := (limit.range B₀).mp hB₀
  obtain ⟨a, _, _, b₀, _, _, hab₀, _⟩ := (source.nodes u₀).mp (limit.projection.bound_l hu₀).1
  obtain ⟨n, a', b, b', _, fa, fa', assign, _, _, hab, hab', code, code'⟩ :=
    source.copy_index_l hZF hω mx my map hℓ length length' target (table.bound_l hab₀).1
  obtain ⟨Dg, Dg', _, _, _, _, _, _, _, _, _, _, D, D', S₀, S₁, _, j, i₀, i₁,
    _, _, _, data, data', _, _, hj, _, _, classes, _, hi₀, hi₁, cs₀, cs₁, square, _⟩ :=
    component a a' n b b' fa fa' assign code code'
  have m₀ : Smdl_d I b D S₀ := by
    obtain ⟨_, _, _, _, _, _, frame⟩ := data
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, quotient⟩ := frame
    exact quotient.code
  have m₁ : Smdl_d I b' D' S₁ := by
    obtain ⟨_, _, _, _, _, _, frame⟩ := data'
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, quotient⟩ := frame
    exact quotient.code
  obtain ⟨s, hs, ss⟩ := source.stage_l hZF hω diagram limit model hab m₀
  obtain ⟨s', hs', ss'⟩ := target.stage_l hZF hω diagram' limit' model' hab' m₁
  obtain ⟨i, hi, is⟩ := smap_comp_l I hZF hi₀ hs
  obtain ⟨i', hi', is'⟩ := smap_comp_l I hZF hi₁ hs'
  have const₀ : Er_constants_d X q i := by
    intro x E hxE
    obtain ⟨_, B, hxB, hBE⟩ := (is x E).mp hxE
    obtain ⟨_, g, fg, hg, constant, _⟩ := (cs₀ x B).mp hxB
    obtain ⟨_, u, hu, huE⟩ := (ss B E).mp hBE
    exact ⟨a, Dg, g, fg, constant, u, B, hu, hg, huE⟩
  have const₁ : Er_constants_d Y q' i' := by
    intro x E hxE
    obtain ⟨_, B, hxB, hBE⟩ := (is' x E).mp hxE
    obtain ⟨_, g, fg, hg, constant, _⟩ := (cs₁ x B).mp hxB
    obtain ⟨_, u, hu, huE⟩ := (ss' B E).mp hBE
    exact ⟨a', Dg', g, fg, constant, u, B, hu, hg, huE⟩
  have constants x x' B E (hxx : Rd_entry_d x x' π) (hxB : Rd_entry_d x B i) :
      Rd_entry_d B E τ ↔ Rd_entry_d x' E i' := by
    obtain ⟨_, B₁, hxB₁, hB₁B⟩ := (is x B).mp hxB
    obtain ⟨B₂, hB₂, hB₁B₂⟩ := hj.1.1.2.2 B₁ (hi₀.1.1.output_mem_of_pairMember hxB₁)
    have hxB₂ := (square x x' B₁ B₂ hxx hxB₁).mp hB₁B₂
    obtain ⟨E₀, _, hB₂E₀⟩ := hs'.1.1.2.2 B₂ hB₂
    have hxE₀ := (is' x' E₀).mpr ⟨hi₁.1.1.input_mem_of_pairMember hxB₂, B₂, hxB₂, hB₂E₀⟩
    obtain ⟨_, u, hu, huB⟩ := (ss B₁ B).mp hB₁B
    obtain ⟨_, v, hv, hvE⟩ := (ss' B₂ E₀).mp hB₂E₀
    have hBE := law u B E₀ huB ((spec u E₀).mpr ⟨(limit.projection.bound_l huB).1,
      a, B₁, a', B₂, v, hu, (classes B₁ B₂).mp hB₁B₂, hv, hvE⟩)
    exact ⟨fun h => hτ.1.1.1.2 B E₀ E hBE h ▸ hxE₀, fun h => hi'.1.1.1.2 x' E₀ E hxE₀ h ▸ hBE⟩
  have allConstants s s' (fs : Fn0_d X C s) (fs' : Fn0_d Y C' s') (cs : Er_constants_d X q s) (cs' : Er_constants_d Y q' s') :
      ∀ x x' B E, Rd_entry_d x x' π → Rd_entry_d x B s → (Rd_entry_d B E τ ↔ Rd_entry_d x' E s') := by
    have eq := source.constants_unique_l hZF mx.2.1 (kp_pair_l hN) hN.1 w ξ ℓ f numbers length loc diagram limit
      fs (fn0_of_function_l (ZF.modelsKP hZF) hi.1.1) cs const₀
    have next := loc.map_l hZF hω mx my map hw hξ hℓ hf
    have eq' := target.constants_unique_l hZF my.2.1 (kp_pair_l hN') hN'.1 w' ξ' ℓ' f' numbers' length' next diagram' limit'
      fs' (fn0_of_function_l (ZF.modelsKP hZF) hi'.1.1) cs' const₁
    subst s s'
    exact constants
  -- 任意实际支撑的坐标类沿同一分量复制，随后进入原先给定的两个极限。
  have seeds a a' n B E (fa : Fn0_d n L a) (fa' : Fn0_d n L' a') (assign : Smap_assign_d I n σ a a')
      (left : Er_seed_d I ω L N T ξ.val f.val z X R k q a B)
      (right : Er_seed_d I ω L' N' T' ξ'.val f'.val z' Y S k' q' a' E) : Rd_entry_d B E τ := by
    obtain ⟨o₀, n₀, m₀, b₀, d₀, u₀, D₀, i₀, t₀, y₀, U₀, G₀, p₀, C₀, W₀, B₀, v₀, frame, htB, pv, hvB⟩ := left
    obtain ⟨o₁, n₁, m₁, b₁, d₁, u₁, D₁, i₁, t₁, y₁, U₁, G₁, p₁, C₁, W₁, B₁, v₁, frame', htE, pv', hvE⟩ := right
    obtain ⟨D₂, D₃, t₂, t₃, y₂, y₃, U₂, U₃, G₂, G₃, p₂, p₃, C₂, C₃, W₂, W₃, _, j, _, _,
      _, _, _, data, data', _, _, _, _, _, classes, _, _, _, _, _, _, coordinate⟩ :=
      component a a' n o₀ o₁ fa fa' assign
        ⟨n₀, m₀, b₀, d₀, u₀, D₀, i₀, t₀, y₀, U₀, G₀, p₀, C₀, W₀, frame⟩
        ⟨n₁, m₁, b₁, d₁, u₁, D₁, i₁, t₁, y₁, U₁, G₁, p₁, C₁, W₁, frame'⟩
    obtain ⟨_, _, _, _, _, _, made⟩ := data
    obtain ⟨_, _, _, _, _, _, made'⟩ := data'
    have owned := loc.read_l I mx.2.1 (kp_pair_l hN) hN.1 w ξ ℓ f
    have next := loc.map_l hZF hω mx my map hw hξ hℓ hf
    have owned' := next.read_l I my.2.1 (kp_pair_l hN') hN'.1 w' ξ' ℓ' f'
    -- 分量唯一性识别两端坐标图及商投影，随后使用同一实际坐标类。
    obtain ⟨_, _, _, _, _, _, rfl, _, rfl, _, _, _, rfl, _, _⟩ :=
      frame.unique_l hZF numbers hN.1 ξ f owned.measures.function agree.injection.1.1 made
    obtain ⟨_, _, _, _, _, _, rfl, _, rfl, _, _, _, rfl, _, _⟩ :=
      frame'.unique_l hZF numbers' hN'.1 ξ' f' owned'.measures.function agree'.injection.1.1 made'
    exact law v₀ B E hvB ((spec v₀ E).mpr ⟨(limit.projection.bound_l hvB).1,
      a, B₀, a', B₁, v₁, pv, (classes B₀ B₁).mp (coordinate B₀ B₁ htB htE), pv', hvE⟩)
  refine ⟨τ, i, i', hτ, hi, hi', const₀, const₁, fun B E => ⟨?_, ?_⟩, constants, allConstants,
    fun r fr hr => unique r fr (fun u B E hu hE => hr u B E hu ((spec u E).mp hE).2),
    fun wf => wf_of_map_l hZF wf (fn0_of_function_l (ZF.modelsKP hZF) hτ.1.1)
      (fun x y x' y' hxy hx hy => (hτ.relation_l I hZF hω model model' hx hy).mp hxy), seeds⟩
  · intro hBE
    have hB := hτ.1.1.input_mem_of_pairMember hBE
    obtain ⟨u, huB⟩ := (limit.range B).mp hB
    obtain ⟨E₀, _, huE₀⟩ := fQ.2.2 u (limit.projection.bound_l huB).1
    have eq := hτ.1.1.1.2 B E₀ E (law u B E₀ huB huE₀) hBE
    exact ⟨hB, u, huB, eq ▸ ((spec u E₀).mp huE₀).2⟩
  · rintro ⟨_, u, huB, copied⟩
    exact law u B E huB ((spec u E).mpr ⟨(limit.projection.bound_l huB).1, copied⟩)

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 工作模型中原关系坐标的实际支撑值

所属数字图和共同图为实际恒等限制时，原坐标代表就是有限幂上的恒等图。
原测度迹等于给定测度，因此同一个商投影产生实际代表；正常坍塌随后
把整条坐标列识别为给定支撑。只在工作模型一侧使用隶属呈示。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Er_seed_d.read_mem_l {ω L N T κ F z Y S k q a E c : M.Domain}
    (hω : M.IsOmega ω) (fs : Fs_read_d ω N) (mx : Smem_d I c N T)
    (zs : ∀ n m, Rd_entry_d n m z ↔ M.mem n ω ∧ n = m)
    (ks : ∀ x y, Rd_entry_d x y k → x = y)
    (family : Em_source_d ω κ L Y F) (seed : Er_seed_d I ω L N T κ F z Y S k q a E) :
    ∃ n D t, M.mem n ω ∧ Fn0_d n L a ∧ Ep_space_d κ n D ∧ Fn0_d D Y t ∧
      (∀ s x, Rd_entry_d s x t → s = x) ∧ Ep_repr_d q a t E := by
  obtain ⟨o, n, m, b, d, u, D, i, t, y, V, G, p, C, W, B, v, frame, htB, pair, hvE⟩ := seed
  obtain ⟨hn, fa, hnm, fb, ga, space, value, dc, fi, id, rt, _, measure, _, quotient⟩ := frame
  obtain ⟨_, rfl⟩ := (zs n m).mp hnm
  have fn := ((rf_fun_mem_l I hZF.1 fs.transitive mx (fs.transitive ω fs.omega_mem n hn)).mp fb).function_l fs.transitive
  have eq := fn.ext_l hZF.1 fa (fun j hj => by
    obtain ⟨x, _, hjx⟩ := fa.2.1 j hj
    exact ⟨x, (rf_val_mem_l I hZF.1 fs.transitive mx (fb.mem_l I)).mp
      ((ga j j x ((zs j j).mpr ⟨hω.transitive (ZF.modelsKP hZF) n hn j hj, rfl⟩)).mp hjx), hjx⟩)
  subst b
  have hκ : M.mem κ N := space.elim fun h _ => h 2
  obtain ⟨hd, ds⟩ := (er_space_mem_l I hZF.1 fs mx hκ hn).mp space
  have eq := hZF.1.eq_of_same_members D d (fun s => (dc s).trans
    ⟨fun h => ((mx.2 s d).mp h.2).2.2,
      fun hs => ⟨fs.transitive d hd s hs, (mx.2 s d).mpr ⟨fs.transitive d hd s hs, hd, hs⟩⟩⟩)
  subst D
  have actual := (rf_val_mem_l I hZF.1 fs.transitive mx (value.bounds_l I).2.2).mp value
  have base := (family.at_l hZF.1 actual fa ds).base
  have hu := (value.bounds_l I).2.1
  -- 恒等坐标把原测度迹逐项还原为同一个实际测度。
  have trace A (hA : M.mem A u) : Rt_trace_d I d i T A A := by
    have ha := fs.transitive u hu A hA
    intro s
    constructor
    · intro hs
      have hsD := base.bounds A hA s hs
      exact ⟨hsD, s, (id s s).mpr ⟨hsD, rfl⟩,
        (mx.2 s A).mpr ⟨fs.transitive d hd s hsD, ha, hs⟩⟩
    · rintro ⟨_, x, hsx, hxA⟩
      exact ((id s x).mp hsx).2 ▸ ((mx.2 x A).mp hxA).2.2
  have eq : V = u := hZF.1.eq_of_same_members V u (fun A => by
    constructor
    · intro hA
      obtain ⟨B, _, hBu, tr⟩ := (measure A).mp hA
      have hb := ((mx.2 B u).mp hBu).2.2
      have eq := hZF.1.eq_of_same_members A B (fun s => (tr s).trans (trace B hb s).symm)
      exact eq.symm ▸ hb
    · intro hA
      have ha := fs.transitive u hu A hA
      exact (measure A).mpr ⟨A, ha, (mx.2 A u).mpr ⟨ha, hu, hA⟩, trace A hA⟩)
  subst V
  exact ⟨n, d, t, hn, fa, ds, quotient.map.functions t (quotient.map.projection.input_mem_of_pairMember htB),
    fun s x hsx => ks s x ((rt.2 s x).mp hsx).2,
    v, B, pair, quotient.map.representative_l I base htB, hvE⟩

section Collapse
variable (hZFC : M.Models ZFC)
local notation "hZ" => ZFC.models_zf_l hZFC
local notation "Kp" => kp_pair_l (ZF.modelsKP hZ)

/-- 实际工作超幂中的整条原坐标值就是给定支撑列。 -/
theorem Er_seed_d.collapse_l
    {ω κ K L X R F J O Z A p T V q c C W d Y S e N R₀ c₀ z k a E : M.Domain}
    (source : Ep_source_d Kp ω κ K X R) (family : Em_source_d ω κ L X F)
    (coherent : Ec_source_d Kp ω κ L X F)
    (system : Ep_system_d Kp ω κ L X R F J O Z A p T V) (limit : Di_limit_d A p T V q C W)
    (model : Smdl_d Kp c C W) (trans : M.TransitiveSet Y) (target : Smem_d Kp d Y S)
    (he : Smap_d Kp ω c d C Y e)
    (fixed : ∀ α B, Ep_seed_d κ L q α B → Rd_entry_d B α e)
    (fs : Fs_read_d ω N) (owner : Smem_d Kp c₀ N R₀)
    (zs : ∀ n m, Rd_entry_d n m z ↔ M.mem n ω ∧ n = m)
    (ks : ∀ x y, Rd_entry_d x y k → x = y)
    (seed : Er_seed_d Kp ω L N R₀ κ F z X R k q a E) : Rd_entry_d E a e := by
  obtain ⟨n, D, t, hn, fa, ds, ft, id, rep⟩ := seed.read_mem_l hZ source.omega fs owner zs ks family
  have ht := (rep.source_l hZ family system limit).1
  have fn := ft.retarget_l (fun s x hsx => id s x hsx ▸ (ft.bound_l hsx).1)
  obtain ⟨r, fr, rs⟩ := fn0_identity_l (ZF.modelsKP hZ) n
  have comp B s (f : Fn0_d n B s) : Cp0_d n n B r s s := ⟨f, fun i hi => by
    obtain ⟨x, hx, hix⟩ := f.2.1 i hi
    exact ⟨i, hi, x, hx, (rs i i).mpr ⟨hi, rfl⟩, hix, hix⟩⟩
  have value := ep_tuple_value_l hZFC source family coherent system limit model trans target he fixed
    (rep.index_l hZ system limit) hn hn fa fr (comp L a fa) ds ds ht fn
    (fun s x hsx => id s x hsx ▸ comp κ s ((ds s).mp (ft.bound_l hsx).1))
  have hE : M.mem E C := by
    obtain ⟨_, _, _, _, huE⟩ := rep
    exact (limit.projection.bound_l huE).2
  obtain ⟨x, _, hEx⟩ := he.1.1.2.2 E hE
  have eq := (Ep_value_d.unique_l hZ family system limit
    (fn0_of_function_l (ZF.modelsKP hZ) he.1.1) ⟨E, rep, hEx⟩ value)
  exact eq ▸ hEx

end Collapse
end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原有界池的完整实现与复制交换

前驱共同层的两条复合图先确定每个实际有界函数码的像。
所属图搬运同一个池节点与坍塌值，原求值复制随后沿实现图下降。
结论给出下一共同层的实际复合图；所有池分解与实现数据均由 raw_present_l 构造。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 首轮的共同层取原生层的全部对象码；任意给定初等图自动产生真实交换方块。 -/
theorem er_common_start_l {ω c N T c' N' T' σ : M.Domain}
    (hω : M.IsOmega ω) (mx : Smdl_d I c N T) (my : Smdl_d I c' N' T')
    (map : Smap_d I ω c c' N N' σ)
    (U : (smdl_structure_l I (R := T) mx.2.1).Domain)
    (U' : (smdl_structure_l I (R := T') my.2.1).Domain)
    (hU : Rd_entry_d U.val U'.val σ) (trans : (smdl_structure_l I (R := T) mx.2.1).TransitiveSet U) :
    ∃ Γ Γ' k k' θ,
      (∀ x, M.mem x Γ ↔ M.mem x N ∧ Rd_entry_d x U.val T) ∧
      (∀ x, M.mem x Γ' ↔ M.mem x N' ∧ Rd_entry_d x U'.val T') ∧
      M.IsSetInjectionFromTo I k Γ N ∧ M.IsSetInjectionFromTo I k' Γ' N' ∧
      (∀ x y, Rd_entry_d x y k ↔ M.mem x Γ ∧ x = y) ∧
      (∀ x y, Rd_entry_d x y k' ↔ M.mem x Γ' ∧ x = y) ∧
      (∀ y, Rd_entry_d y U.val T ↔ ∃ x, M.mem x Γ ∧ Rd_entry_d x y k) ∧
      (∀ y, Rd_entry_d y U'.val T' ↔ ∃ x, M.mem x Γ' ∧ Rd_entry_d x y k') ∧
      (∀ x y, Rd_entry_d x y k → ∀ v, Rd_entry_d v y T ↔ ∃ a, Rd_entry_d a x T ∧ Rd_entry_d a v k) ∧
      (∀ x y, Rd_entry_d x y k' → ∀ v, Rd_entry_d v y T' ↔ ∃ a, Rd_entry_d a x T' ∧ Rd_entry_d a v k') ∧
      Fn0_d Γ N' θ ∧ It_comp_d k σ θ ∧ It_comp_d σ k' θ := by
  have cut {c N T : M.Domain} (model : Smdl_d I c N T)
      (U : (smdl_structure_l I (R := T) model.2.1).Domain)
      (trans : (smdl_structure_l I (R := T) model.2.1).TransitiveSet U) :
      ∃ Γ k, (∀ x, M.mem x Γ ↔ M.mem x N ∧ Rd_entry_d x U.val T) ∧
        M.IsSetInjectionFromTo I k Γ N ∧
        (∀ x y, Rd_entry_d x y k ↔ M.mem x Γ ∧ x = y) ∧
        (∀ y, Rd_entry_d y U.val T ↔ ∃ x, M.mem x Γ ∧ Rd_entry_d x y k) ∧
        ∀ x y, Rd_entry_d x y k → ∀ v, Rd_entry_d v y T ↔ ∃ a, Rd_entry_d a x T ∧ Rd_entry_d a v k := by
    let ρ : Env M 2 := ⟨Fin.cases U.val (fun _ => T), fun _ => N⟩
    let φ : UnarySchema 2 := { body := rd_entry0_m .newest (.bound 1) (.bound 2) }
    obtain ⟨Γ, sep⟩ := ZF.separation_exists_d hZF φ ρ N
    have carrier x : M.mem x Γ ↔ M.mem x N ∧ Rd_entry_d x U.val T :=
      (sep x).trans (and_congr_right fun _ => rd_entry0_sat_l hZF.1 ..)
    obtain ⟨k, fk, id⟩ := fn0_identity_l (ZF.modelsKP hZF) Γ
    have fn := fn0_function_l (ZF.modelsKP hZF) (fk.mono_target_l (fun x hx => ((carrier x).mp hx).1))
    refine ⟨Γ, k, carrier, ⟨fn, fun x y z hx hy => ((id x z).mp hx).2.trans ((id y z).mp hy).2.symm⟩,
      id, fun y => ?_, fun x y hxy v => ?_⟩
    · constructor
      · intro hy
        have hx := (carrier y).mpr ⟨(model.2.2.2 y U.val hy).1, hy⟩
        exact ⟨y, hx, (id y y).mpr ⟨hx, rfl⟩⟩
      · rintro ⟨x, hx, hxy⟩
        exact ((id x y).mp hxy).2 ▸ ((carrier x).mp hx).2
    · obtain ⟨hx, rfl⟩ := (id x y).mp hxy
      constructor
      · intro hv
        have hvN := (model.2.2.2 v x hv).1
        have hvΓ := (carrier v).mpr ⟨hvN, trans ⟨x, ((carrier x).mp hx).1⟩ ((carrier x).mp hx).2 ⟨v, hvN⟩ hv⟩
        exact ⟨v, hv, (id v v).mpr ⟨hvΓ, rfl⟩⟩
      · rintro ⟨a, ha, hav⟩
        exact ((id a v).mp hav).2 ▸ ha
  have trans' : (smdl_structure_l I (R := T') my.2.1).TransitiveSet U' :=
    (Formula.satisfies_isTransitive_iff ..).mp
      ((smap_source_l I hZF hω mx my map (n := 1) (Formula.isTransitive .newest)
        (by simp -implicitDefEqProofs) ⟨fun _ => U, fun _ => U⟩ ⟨fun _ => U', fun _ => U'⟩
        (fun _ => hU)).mp ((Formula.satisfies_isTransitive_iff ..).mpr trans))
  obtain ⟨Γ, k, carrier, fk, id, image, pred⟩ := cut mx U trans
  obtain ⟨Γ', k', carrier', fk', id', image', pred'⟩ := cut my U' trans'
  obtain ⟨θ, fθ, graph⟩ := ZF.exists_compositionFunction hZF I fk.1 map.1.1
  have first : It_comp_d k σ θ := ⟨fθ.1.1, fun x y => (graph x y).trans
    ⟨And.right, fun ⟨a, hxa, hay⟩ => ⟨fk.1.input_mem_of_pairMember hxa, a, hxa, hay⟩⟩⟩
  refine ⟨Γ, Γ', k, k', θ, carrier, carrier', fk, fk', id, id', image, image', pred, pred',
    fn0_of_function_l (ZF.modelsKP hZF) fθ, first, fθ.1.1, fun x y => ?_⟩
  constructor
  · intro hxy
    obtain ⟨a, hxa, hay⟩ := (first.2 x y).mp hxy
    obtain ⟨hx, rfl⟩ := (id x a).mp hxa
    have hy := (carrier' y).mpr ⟨map.1.1.output_mem_of_pairMember hay,
      (map.relation_l I hZF hω mx my hay hU).mp ((carrier x).mp hx).2⟩
    exact ⟨y, hay, (id' y y).mpr ⟨hy, rfl⟩⟩
  · rintro ⟨a, hxa, hay⟩
    obtain ⟨ha, rfl⟩ := (id' a y).mp hay
    have hx := (carrier x).mpr ⟨map.1.1.input_mem_of_pairMember hxa,
      (map.relation_l I hZF hω mx my hxa hU).mpr ((carrier' a).mp ha).2⟩
    exact (first.2 x a).mpr ⟨x, (id x x).mpr ⟨hx, rfl⟩, hxa⟩

private def er_present_base_m {d} (U w ξ β X K δ : Term d) : Formula 1 d := set[d] ⟪
  ⌜fs_read_m⌝ₚ(⌜w⌝ₛ, ⌜U⌝ₛ) ∧
  (∀ m D, m ∈ ⌜w⌝ₛ → ⌜ep_space_m⌝ₚ(⌜ξ⌝ₛ, m, D) →
    ∃ P ∈ ⌜U⌝ₛ, ⌜Formula.isCartesianProduct kpair_convention_l⌝ₚ(P, D, ⌜β⌝ₛ)) ∧
  ⌜fseq_space_m (𝒞 := kpair_convention_l)⌝ₚ(⌜w⌝ₛ, ⌜ξ⌝ₛ, ⌜K⌝ₛ) ∧ ⌜K⌝ₛ ∈ ⌜X⌝ₛ ∧
  ⌜v_sigma_m⌝ₚ(⌜δ⌝ₛ, ⌜X⌝ₛ) ∧ ⌜Formula.isLimitOrdinal⌝ₚ(⌜δ⌝ₛ) ∧ ⌜β⌝ₛ ∈ ⌜X⌝ₛ ∧
  ⌜Formula.isTransitive⌝ₚ(⌜β⌝ₛ) ∧ ⌜ξ⌝ₛ ∈ ⌜U⌝ₛ⟫
derive_free_closed er_present_base_m

private theorem er_present_base_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (U w ξ β X K δ : Term d) :
    Formula.satisfies ρ (er_present_base_m U w ξ β X K δ) ↔
      Fs_read_d (w.eval ρ) (U.eval ρ) ∧
      (∀ m D, M.mem m (w.eval ρ) → Ep_space_d (ξ.eval ρ) m D →
        ∃ P, M.mem P (U.eval ρ) ∧ M.IsCartesianProduct (kp_pair_l hKP) P D (β.eval ρ)) ∧
      Fseq_space_d (kp_pair_l hKP) (w.eval ρ) (ξ.eval ρ) (K.eval ρ) ∧ M.mem (K.eval ρ) (X.eval ρ) ∧
      V_d (kp_pair_l hKP) (δ.eval ρ) (X.eval ρ) ∧ M.IsLimitOrdinal (δ.eval ρ) ∧
      M.mem (β.eval ρ) (X.eval ρ) ∧ M.TransitiveSet (β.eval ρ) ∧ M.mem (ξ.eval ρ) (U.eval ρ) := by
  simp only [er_present_base_m, Formula.satisfies_conj_iff, fs_read_sat_l hKP.1,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Formula.satisfies_mem_iff,
    ep_space_sat_l hKP.1, Formula.satisfies_existsMem_iff, Formula.satisfies_isCartesianProduct_iff (kp_pair_l hKP),
    fseq_space_sat_l (kp_pair_l hKP) hKP.1, v_sigma_sat_l hKP, Formula.satisfies_isLimitOrdinal_iff,
    Formula.satisfies_isTransitive_iff, Definitional.Term.eval_weaken]; rfl

/-- 同一原池的目标实现自动构造，旧方块下降为 τ∘t=t'∘σ。 -/
theorem er_present_copy_l
    {ω c N T c' N' T' σ L L' z z' Γ Γ' X R Y S k k' π θ
      J O Z A p V W q C Q J' O' Z' A' p' V' W' q' C' Q'
      D B t τ b h' o' j' H' : M.Domain}
    (hω : M.IsOmega ω) (mx : Smdl_d I c N T) (my : Smdl_d I c' N' T')
    (map : Smap_d I ω c c' N N' σ)
    (hN : (smdl_structure_l I (R := T) mx.2.1).Models KP)
    (nx : ∃ x, M.mem x X) (ny : ∃ y, M.mem y Y)
    (ex : Extensional (smdl_structure_l I (R := R) nx))
    (ey : Extensional (smdl_structure_l I (R := S) ny))
    (copy : M.IsSetFunctionFromTo I π X Y)
    (U w ξ ℓ e β A₀ B₀ e₀ : (smdl_structure_l I (R := T) mx.2.1).Domain)
    (U' w' ξ' ℓ' e' β' A₁ B₁ e₁ : (smdl_structure_l I (R := T') my.2.1).Domain)
    (X₀ K₀ δ Q₀ H₀ : (smdl_structure_l I (R := T) mx.2.1).Domain)
    (hU : Rd_entry_d U.val U'.val σ) (hF : Rd_entry_d e.val e'.val σ)
    (hξ : Rd_entry_d ξ.val ξ'.val σ) (hℓ : Rd_entry_d ℓ.val ℓ'.val σ)
    (hβ : Rd_entry_d β.val β'.val σ) (hA : Rd_entry_d A₀.val A₁.val σ)
    (hB : Rd_entry_d B₀.val B₁.val σ) (he : Rd_entry_d e₀.val e₁.val σ)
    (numbers : Rr_layer_d I ω N T w.val z) (numbers' : Rr_layer_d I ω N' T' w'.val z')
    (finite : Fs_read_d w U) (ownerClosed : Rr_closed_d I N T U.val)
    (products : ∀ m d : (smdl_structure_l I (R := T) mx.2.1).Domain,
      (smdl_structure_l I (R := T) mx.2.1).mem m w → Ep_space_d ξ m d →
      ∃ P, (smdl_structure_l I (R := T) mx.2.1).mem P U ∧
        (smdl_structure_l I (R := T) mx.2.1).IsCartesianProduct (kp_pair_l hN) P d β)
    (sequences : Fseq_space_d (kp_pair_l hN) w ξ K₀)
    (support : Fseq_space_d (kp_pair_l hN) w ℓ H₀)
    (hK : (smdl_structure_l I (R := T) mx.2.1).mem K₀ X₀)
    (rank : V_d (kp_pair_l hN) δ X₀) (height : (smdl_structure_l I (R := T) mx.2.1).IsLimitOrdinal δ)
    (hβX : (smdl_structure_l I (R := T) mx.2.1).mem β X₀)
    (transβ : (smdl_structure_l I (R := T) mx.2.1).TransitiveSet β)
    (hξU : (smdl_structure_l I (R := T) mx.2.1).mem ξ U)
    (pool : Eb_collapse_d w ξ ℓ K₀ X₀ β e A₀ Q₀ B₀ e₀)
    (loc : It_local_d I w.val N T ξ.val ℓ.val e.val)
    (carrier : ∀ x, M.mem x Γ ↔ M.mem x N ∧ Rd_entry_d x U.val T)
    (carrier' : ∀ x, M.mem x Γ' ↔ M.mem x N' ∧ Rd_entry_d x U'.val T')
    (fk : M.IsSetInjectionFromTo I k Γ X) (fk' : M.IsSetInjectionFromTo I k' Γ' Y)
    (pred : ∀ x y, Rd_entry_d x y k → ∀ a, Rd_entry_d a y R ↔ ∃ u, Rd_entry_d u x T ∧ Rd_entry_d u a k)
    (pred' : ∀ x y, Rd_entry_d x y k' → ∀ a, Rd_entry_d a y S ↔ ∃ u, Rd_entry_d u x T' ∧ Rd_entry_d u a k')
    (target : Smdl_d I h' Y S) (targetTheory : Sc_theory_d I ω Y S)
    (targetImage : ∀ y, Rd_entry_d y H' S ↔ ∃ x, M.mem x Γ' ∧ Rd_entry_d x y k')
    (targetClosed : Rr_closed_d I Y S H')
    (old : It_comp_d k π θ) (owned : It_comp_d σ k' θ) (hβb : Rd_entry_d β.val b k)
    (length : ∀ x, M.mem x L ↔ M.mem x N ∧ Rd_entry_d x ℓ.val T)
    (length' : ∀ x, M.mem x L' ↔ M.mem x N' ∧ Rd_entry_d x ℓ'.val T')
    (system : Er_graph_d I ω L N T ξ.val ℓ.val e.val z X R k J O Z A p V W)
    (system' : Er_graph_d I ω L' N' T' ξ'.val ℓ'.val e'.val z' Y S k' J' O' Z' A' p' V' W')
    (limit : Di_limit_d A p V W q C Q) (limit' : Di_limit_d A' p' V' W' q' C' Q')
    (diagram' : Di_system_d J' O' A' p' V' W') (next : Smdl_d I o' C' Q')
    (embed : Smap_d I ω h' o' Y C' j') (constants : Er_constants_d Y q' j')
    (fτ : Fn0_d C C' τ)
    (copied : ∀ E E', Rd_entry_d E E' τ ↔ M.mem E C ∧ ∃ x, Rd_entry_d x E q ∧
      Er_node_d I ω L N T ξ.val e.val z X R k L' N' T' ξ'.val e'.val z' Y S k' π σ q' x E')
    (dc : ∀ u, M.mem u D ↔ M.mem u N ∧ Rd_entry_d u A₀.val T)
    (bc : ∀ x, M.mem x B ↔ M.mem x N ∧ Rd_entry_d x B₀.val T)
    (ft : Fn0_d B C t)
    (present : Er_present_d I ω L N T z Γ X k q e₀.val D t)
    (prepare : ∀ u : (smdl_structure_l I (R := T) mx.2.1).Domain,
      (smdl_structure_l I (R := T) mx.2.1).mem u A₀ →
      ∃ α, ∃ m a d f : (smdl_structure_l I (R := T) mx.2.1).Domain,
        Ei_d ω L α ∧ Rr_finite_d I ω L N T z α a.val ∧
        (smdl_structure_l I (R := T) mx.2.1).mem m w ∧ Fn0_d m ℓ a ∧ Ep_space_d ξ m d ∧
        (smdl_structure_l I (R := T) mx.2.1).mem f U ∧ Fn0_d d β f ∧
        KPair_d (smdl_structure_l I (R := T) mx.2.1) u a f) :
    let hN' := map.native_models_l hZF hω mx my hN
    ∃ X₁ K₁ δ₁ Q₁ H₁ : (smdl_structure_l I (R := T') my.2.1).Domain,
      Rd_entry_d X₀.val X₁.val σ ∧ Rd_entry_d K₀.val K₁.val σ ∧
      Rd_entry_d δ.val δ₁.val σ ∧ Rd_entry_d Q₀.val Q₁.val σ ∧ Rd_entry_d H₀.val H₁.val σ ∧
      Fseq_space_d (kp_pair_l hN') w' ξ' K₁ ∧ Fseq_space_d (kp_pair_l hN') w' ℓ' H₁ ∧
      V_d (kp_pair_l hN') δ₁ X₁ ∧ (smdl_structure_l I (R := T') my.2.1).IsLimitOrdinal δ₁ ∧
      (smdl_structure_l I (R := T') my.2.1).mem K₁ X₁ ∧ (smdl_structure_l I (R := T') my.2.1).mem β' X₁ ∧
      Eb_collapse_d w' ξ' ℓ' K₁ X₁ β' e' A₁ Q₁ B₁ e₁ ∧
    ∃ D' B' v' t',
      (∀ u, M.mem u D' ↔ M.mem u N' ∧ Rd_entry_d u A₁.val T') ∧
      (∀ x, M.mem x B' ↔ M.mem x N' ∧ Rd_entry_d x B₁.val T') ∧
      Fn0_d D' C' v' ∧
      (∀ u E, Rd_entry_d u E v' ↔ M.mem u D' ∧ Er_eval_d I ω L' N' T' z' Γ' Y k' q' u E) ∧
      M.IsSetInjectionFromTo I t' B' C' ∧ Er_present_d I ω L' N' T' z' Γ' Y k' q' e₁.val D' t' ∧
      (∀ x x' E E', Rd_entry_d x x' σ → Rd_entry_d x E t →
      (Rd_entry_d E E' τ ↔ Rd_entry_d x' E' t')) ∧
    ∃ ψ, Fn0_d B C' ψ ∧ It_comp_d t τ ψ ∧ It_comp_d σ t' ψ := by
  let N₀ := smdl_structure_l I (R := T) mx.2.1
  let N₁ := smdl_structure_l I (R := T') my.2.1
  have hN' := map.native_models_l hZF hω mx my hN
  have en := hN.1
  have en' := hN'.1
  have ext : Rf_ext_d I N T := fun x hx y hy same => congrArg Subtype.val
    (en.eq_of_same_members ⟨x, hx⟩ ⟨y, hy⟩ (fun z => same z.val z.property))
  have hw := (numbers.omega_map_l I hZF hω mx my map ext
    (map.extensional_l hZF hω mx my ext) numbers').1
  obtain ⟨x₁, hx₁, hX⟩ := map.1.1.2.2 X₀.val X₀.property
  obtain ⟨k₁, hk₁, hKK⟩ := map.1.1.2.2 K₀.val K₀.property
  obtain ⟨δ₁, hδ₁, hδ⟩ := map.1.1.2.2 δ.val δ.property
  obtain ⟨q₁, hq₁, hQQ⟩ := map.1.1.2.2 Q₀.val Q₀.property
  let X₁ : N₁.Domain := ⟨x₁, hx₁⟩
  let K₁ : N₁.Domain := ⟨k₁, hk₁⟩
  let δ' : N₁.Domain := ⟨δ₁, hδ₁⟩
  let Q₁ : N₁.Domain := ⟨q₁, hq₁⟩
  let ρ : Env N₀ 7 := ⟨fun i => [U, w, ξ, β, X₀, K₀, δ].get i, fun _ => w⟩
  let η : Env N₁ 7 := ⟨fun i => [U', w', ξ', β', X₁, K₁, δ'].get i, fun _ => w'⟩
  let φ : Formula 1 7 := er_present_base_m (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4) (.bound 5) (.bound 6)
  have initial : Formula.satisfies ρ φ := (er_present_base_sat_l hN ρ ..).mpr
    ⟨finite, products, sequences, hK, rank, height, hβX, transβ, hξU⟩
  have moved := (smap_source_l I hZF hω mx my map φ (by simp -implicitDefEqProofs [φ]) ρ η
    (Fin.cases hU (Fin.cases hw (Fin.cases hξ (Fin.cases hβ (Fin.cases hX
      (Fin.cases hKK (Fin.cases hδ (fun i => Fin.elim0 i))))))))).mp initial
  obtain ⟨finite', products', sequences', hK', rank', height', hβX', transβ', hξU'⟩ :=
    (er_present_base_sat_l hN' η (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4) (.bound 5) (.bound 6)).mp moved
  have ownerClosed' := (map.rr_closed_l I hZF hω mx my hU).mp ownerClosed
  obtain ⟨pool', ⟨H₁, hHH, support'⟩, _⟩ := pool.owner_image_l hZF hω mx my map hN hN' w ξ ℓ K₀ X₀ β e A₀ Q₀ B₀ e₀ H₀
    w' ξ' ℓ' K₁ X₁ β' e' A₁ Q₁ B₁ e₁ hw hξ hℓ hKK hX hβ hF hA hQQ hB he support
  have local' := loc.map_l hZF hω mx my map hw hξ hℓ hF
  have trans := finite.transitive
  have trans' := finite'.transitive
  -- 先读前驱的真实复合图，得到具体函数码的像；不把有限幂子集条件扩张使用。
  have commute x x' y (hxx : Rd_entry_d x x' σ) (hxy : Rd_entry_d x y k) :
      ∃ y', Rd_entry_d x' y' k' ∧ Rd_entry_d y y' π := by
    obtain ⟨y', _, hyy⟩ := copy.2.2 y (fk.1.output_mem_of_pairMember hxy)
    obtain ⟨u, hxu, huy⟩ := (owned.2 x y').mp ((old.2 x y').mpr ⟨y, hxy, hyy⟩)
    exact ⟨y', map.1.1.1.2 x u x' hxu hxx ▸ huy, hyy⟩
  obtain ⟨b', hβb', _⟩ := commute β.val β'.val b hβ hβb
  obtain ⟨H₂, _, hbH⟩ := embed.1.1.2.2 b' (fk'.1.output_mem_of_pairMember hβb')
  obtain ⟨a₂, D₂, f₂, ff₂, constant₂, value₂⟩ := constants b' H₂ hbH
  have ey' : Rf_ext_d I Y S := fun x hx y hy same => congrArg Subtype.val
    (ey.eq_of_same_members ⟨x, hx⟩ ⟨y, hy⟩ (fun z => same z.val z.property))
  -- 完整目标实现覆盖目标池的全部节点，包含不在所属嵌入像中的新节点。
  obtain ⟨D', B', s', v', t', dc', bc', _, _, fv', values', _, _, _, it', present', _, _, _⟩ :=
    local'.raw_present_l hZF hω target ey' targetTheory my.2.1 hN' U' w' ξ' ℓ' e' numbers' finite'
      carrier' ownerClosed' fk' targetImage pred' targetClosed hξU' length' β' X₁ K₁ δ' A₁ Q₁ B₁ e₁
      products' sequences' hK' rank' height' hβX' transβ' pool' system' diagram' limit' next embed
      hβb' hbH ff₂ constant₂ value₂
  have ft' := fn0_of_function_l (ZF.modelsKP hZF) it'.1
  have function (a b f : N₀.Domain) (a' b' f' : N₁.Domain)
      (haa : Rd_entry_d a.val a'.val σ) (hbb : Rd_entry_d b.val b'.val σ)
      (hff : Rd_entry_d f.val f'.val σ) (fn : Fn0_d a b f) : Fn0_d a' b' f' := by
    let ρ : Env N₀ 3 := ⟨Fin.cases a (Fin.cases b (fun _ => f)), fun _ => f⟩
    let η : Env N₁ 3 := ⟨Fin.cases a' (Fin.cases b' (fun _ => f')), fun _ => f'⟩
    exact (fn0_sat_l en' η .newest (.bound 1) (.bound 2)).mp
      ((smap_source_l I hZF hω mx my map (fn0_m .newest (.bound 1) (.bound 2))
        (by simp -implicitDefEqProofs) ρ η (Fin.cases haa (Fin.cases hbb (fun _ => hff)))).mp
          ((fn0_sat_l en ρ .newest (.bound 1) (.bound 2)).mpr fn))
  have total x x' E (hxx : Rd_entry_d x x' σ) (hxE : Rd_entry_d x E t) :
      ∃ E', Rd_entry_d E E' τ ∧ Rd_entry_d x' E' t' := by
    obtain ⟨u, hu, hux, value⟩ := (present x E).mp hxE
    let u₀ : N₀.Domain := ⟨u, ((dc u).mp hu).1⟩
    obtain ⟨α, m, a, d, f, _, code, _, fa, ds, hf, ff, pair⟩ := prepare u₀ ((dc u).mp hu).2
    obtain ⟨m₁, hm₁, hmm⟩ := map.1.1.2.2 m.val m.property
    obtain ⟨a₁, ha₁, haa⟩ := map.1.1.2.2 a.val a.property
    obtain ⟨d₁, hd₁, hdd⟩ := map.1.1.2.2 d.val d.property
    obtain ⟨f₁, hf₁, hff⟩ := map.1.1.2.2 f.val f.property
    obtain ⟨u₁, hu₁, huu⟩ := map.1.1.2.2 u u₀.property
    let m' : N₁.Domain := ⟨m₁, hm₁⟩
    let a' : N₁.Domain := ⟨a₁, ha₁⟩
    let d' : N₁.Domain := ⟨d₁, hd₁⟩
    let f' : N₁.Domain := ⟨f₁, hf₁⟩
    let u' : N₁.Domain := ⟨u₁, hu₁⟩
    have huD : M.mem u₁ D' := (dc' u₁).mpr ⟨hu₁,
      (map.relation_l I hZF hω mx my huu hA).mp ((dc u).mp hu).2⟩
    obtain ⟨E', _, huE'⟩ := fv'.2.1 u₁ huD
    have fa' := function m ℓ a m' ℓ' a' hmm hℓ haa fa
    have ff' := function d β f d' β' f' hdd hβ hff ff
    have ds' : Ep_space_d ξ' m' d' := (er_space_native_l I my.2.1 en' ξ' m' d').mp
      (Rr_truth_d.map_l I hZF hω mx my map (by simp -implicitDefEqProofs)
        ((er_space_native_l I mx.2.1 en ξ m d).mpr ds) (Fin.cases hdd (Fin.cases hmm (fun _ => hξ))))
    have pair' : KPair_d N₁ u' a' f' := (rf_pair_native_l I my.2.1 en' u' a' f').mp
      (Rr_truth_d.map_l I hZF hω mx my map (by simp -implicitDefEqProofs)
        ((rf_pair_native_l I mx.2.1 en u₀ a f).mpr pair) (Fin.cases huu (Fin.cases haa (fun _ => hff))))
    have data := code
    obtain ⟨n, _, _, sa, _⟩ := data
    obtain ⟨α', sa', assign, _⟩ := er_support_image_l hZF hω mx my map hℓ length length' sa
    have code' := code.image_l hZF hω mx my map ext numbers numbers' sa sa' assign haa
    obtain ⟨f₀, _, hff₀⟩ := fk.1.2.2 f.val ((carrier f.val).mpr ⟨f.property, hf⟩)
    obtain ⟨f₂, hff₂, image⟩ := commute f.val f₁ f₀ hff hff₀
    obtain ⟨b', hβb', _⟩ := commute β.val β'.val b hβ hβb
    have node := value.copy_node_l hZF numbers numbers' en en' nx ny ex ey
      U u₀ a f m d β ξ ℓ e U' u' a' f' m' d' β' ξ' ℓ' e' trans trans' carrier carrier' fk fk' pred pred'
      code code' fa fa' ds ds' ff ff' pair pair' hβb hβb' hff₀ hff₂ image sa sa' assign
      system system' limit limit' ((values' u₁ E').mp huE').2
    have hxE' : Rd_entry_d x' E' t' := (present' x' E').mpr
      ⟨u₁, huD, hux.map_l I hZF hω mx my map huu hxx he, ((values' u₁ E').mp huE').2⟩
    exact ⟨E', (copied E E').mpr node, hxE'⟩
  have square x x' E E' (hxx : Rd_entry_d x x' σ) (hxE : Rd_entry_d x E t) :
      Rd_entry_d E E' τ ↔ Rd_entry_d x' E' t' := by
    obtain ⟨F, hEF, hxF⟩ := total x x' E hxx hxE
    exact ⟨fun h => (fn0_function_l (ZF.modelsKP hZF) fτ).1.2 E F E' hEF h ▸ hxF,
      fun h => (fn0_function_l (ZF.modelsKP hZF) ft').1.2 x' F E' hxF h ▸ hEF⟩
  -- 在同一新共同层上实际构造复合图，下一次复制可以直接消费这张图。
  obtain ⟨ψ, fψ, graph⟩ := ZF.exists_compositionFunction hZF I
    (fn0_function_l (ZF.modelsKP hZF) ft) (fn0_function_l (ZF.modelsKP hZF) fτ)
  refine ⟨X₁, K₁, δ', Q₁, H₁, hX, hKK, hδ, hQQ, hHH, sequences', support', rank', height', hK', hβX',
    pool', D', B', v', t', dc', bc', fv', values', it', present',
    square, ψ, fn0_of_function_l (ZF.modelsKP hZF) fψ,
    ⟨fψ.1.1, fun x y => (graph x y).trans ⟨And.right,
      fun ⟨E, hxE, hEy⟩ => ⟨(ft.bound_l hxE).1, E, hxE, hEy⟩⟩⟩, fψ.1.1, fun x y => ?_⟩
  constructor
  · intro hxy
    obtain ⟨hx, E, hxE, hEy⟩ := (graph x y).mp hxy
    obtain ⟨x', _, hxx⟩ := map.1.1.2.2 x ((bc x).mp hx).1
    exact ⟨x', hxx, (square x x' E y hxx hxE).mp hEy⟩
  · rintro ⟨x', hxx, hxy⟩
    have hx : M.mem x B := (bc x).mpr ⟨map.1.1.input_mem_of_pairMember hxx,
      (map.relation_l I hZF hω mx my hxx hB).mpr ((bc' x').mp (ft'.bound_l hxy).1).2⟩
    obtain ⟨E, _, hxE⟩ := ft.2.1 x hx
    exact (graph x y).mpr ⟨hx, E, hxE, (square x x' E y hxx hxE).mpr hxy⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 整层复制在实际共同秩段上的限制

完整初等图搬运原秩历史，目标 KP 中的历史比较识别指定层的像。
两侧原实现图的实际限制因而保留同一个复制方块，并构造下一次所用的复合图。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem er_rank_cut_copy_l
    {ω c N T c' N' T' σ ℓ ℓ' U U' D D' C C' t t' u u' τ ψ : M.Domain}
    (hω : M.IsOmega ω) (mx : Smdl_d I c N T) (my : Smdl_d I c' N' T')
    (map : Smap_d I ω c c' N N' σ)
    (hN : (smdl_structure_l I (R := T') my.2.1).Models KP)
    (source : Rr_rank_d I N T ℓ U) (target : Rr_rank_d I N' T' ℓ' U') (hℓ : Rd_entry_d ℓ ℓ' σ)
    (dc : ∀ x, M.mem x D ↔ M.mem x N ∧ Rd_entry_d x U T)
    (dc' : ∀ x, M.mem x D' ↔ M.mem x N' ∧ Rd_entry_d x U' T')
    (res : M.IsRestrictionOf I u t D) (res' : M.IsRestrictionOf I u' t' D')
    (fu : Fn0_d D C u) (fu' : Fn0_d D' C' u') (copy : Fn0_d C C' τ)
    (left : It_comp_d t τ ψ) (right : It_comp_d σ t' ψ) :
    Rd_entry_d U U' σ ∧
      (∀ x x', Rd_entry_d x x' σ → (M.mem x D ↔ M.mem x' D')) ∧
      (∀ x x' E E', Rd_entry_d x x' σ → Rd_entry_d x E u →
        (Rd_entry_d E E' τ ↔ Rd_entry_d x' E' u')) ∧
      ∃ φ, Fn0_d D C' φ ∧ It_comp_d u τ φ ∧ It_comp_d σ u' φ := by
  obtain ⟨hl, hU, rank⟩ := source
  obtain ⟨hl', hU', rank'⟩ := target
  obtain ⟨V, hV, hUV⟩ := map.1.1.2.2 U hU
  let N₁ := smdl_structure_l I (R := T') my.2.1
  let ρ : Env (smdl_structure_l I (R := T) mx.2.1) 2 :=
    ⟨Fin.cases ⟨U, hU⟩ (fun _ => ⟨ℓ, hl⟩), fun _ => ⟨ℓ, hl⟩⟩
  let η : Env N₁ 2 := ⟨Fin.cases ⟨V, hV⟩ (fun _ => ⟨ℓ', hl'⟩), fun _ => ⟨ℓ', hl'⟩⟩
  have moved : V_d (kp_pair_l hN) (⟨ℓ', hl'⟩ : N₁.Domain) ⟨V, hV⟩ :=
    (v_sigma_sat_l hN η (.bound 1) .newest).mp
    ((smap_source_l I hZF hω mx my map (v_sigma_m (.bound 1) .newest)
      (by simp -implicitDefEqProofs) ρ η (Fin.cases hUV (fun _ => hℓ))).mp rank)
  -- 显式读取已有历史的局部递归证书，再与搬运来的历史比较。
  have actual : V_d (kp_pair_l hN) (⟨ℓ', hl'⟩ : N₁.Domain) ⟨U', hU'⟩ := by
    simp only [v_sigma_m, Formula.satisfies_exists_iff, Formula.satisfies_forall_iff,
      vc_matrix_sat_l hN, Definitional.Term.eval_weaken] at rank'
    obtain ⟨B, f, history⟩ := rank'
    exact vc_sound_l hN history
  -- 只比较两份已经存在的秩历史；不要求目标存在全局累积层级。
  have sub := (KP.v_compare_l hN moved actual (fun _ h => h)).1
  have sub' := (KP.v_compare_l hN actual moved (fun _ h => h)).1
  have eq : V = U' := congrArg (fun x : N₁.Domain => x.val) (hN.1.eq_of_same_members (⟨V, hV⟩ : N₁.Domain) ⟨U', hU'⟩
    (fun x => ⟨sub x, sub' x⟩))
  have hUU : Rd_entry_d U U' σ := eq ▸ hUV
  have domain x x' (hxx : Rd_entry_d x x' σ) : M.mem x D ↔ M.mem x' D' :=
    (dc x).trans ((and_iff_right (map.1.1.input_mem_of_pairMember hxx)).trans
      ((map.relation_l I hZF hω mx my hxx hUU).trans
        ((dc' x').trans (and_iff_right (map.1.1.output_mem_of_pairMember hxx))).symm))
  have square x x' E E' (hxx : Rd_entry_d x x' σ) (hxE : Rd_entry_d x E u) :
      Rd_entry_d E E' τ ↔ Rd_entry_d x' E' u' := by
    obtain ⟨F, _, hEF⟩ := copy.2.1 E (fu.bound_l hxE).2
    obtain ⟨y, hxy, hyF⟩ := (right.2 x F).mp ((left.2 x F).mpr ⟨E, ((res.2 x E).mp hxE).2, hEF⟩)
    have hxF : Rd_entry_d x' F u' := (res'.2 x' F).mpr
      ⟨(domain x x' hxx).mp (fu.bound_l hxE).1, map.1.1.1.2 x y x' hxy hxx ▸ hyF⟩
    exact ⟨fun h => (fn0_function_l (ZF.modelsKP hZF) copy).1.2 E F E' hEF h ▸ hxF,
      fun h => (fn0_function_l (ZF.modelsKP hZF) fu').1.2 x' F E' hxF h ▸ hEF⟩
  obtain ⟨φ, fφ, graph⟩ := ZF.exists_compositionFunction hZF I
    (fn0_function_l (ZF.modelsKP hZF) fu) (fn0_function_l (ZF.modelsKP hZF) copy)
  refine ⟨hUU, domain, square, φ, fn0_of_function_l (ZF.modelsKP hZF) fφ,
    ⟨fφ.1.1, fun x E => (graph x E).trans ⟨And.right,
      fun ⟨P, hxP, hPE⟩ => ⟨(fu.bound_l hxP).1, P, hxP, hPE⟩⟩⟩, fφ.1.1, fun x E => ?_⟩
  constructor
  · intro h
    obtain ⟨hx, P, hxP, hPE⟩ := (graph x E).mp h
    obtain ⟨x', _, hxx⟩ := map.1.1.2.2 x ((dc x).mp hx).1
    exact ⟨x', hxx, (square x x' P E hxx hxP).mp hPE⟩
  · rintro ⟨x', hxx, hxE⟩
    have hx := (domain x x' hxx).mpr (fu'.bound_l hxE).1
    obtain ⟨P, _, hxP⟩ := fu.2.1 x hx
    exact (graph x E).mpr ⟨hx, P, hxP, (square x x' P E hxx hxP).mpr hxE⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原池复制在工作集合像中的实际值

所属有界坍塌的完整求值图由同一代表族及坍塌唯一性取得。
工作侧原关系实现经集合像因子还原为该坍塌值，因此整层复制方块
直接给出同一个集合像复制图与所属图的一致性。原生小秩源的池在此直接
读回并提升到完整工作源，有限列空间也自动与该源对齐。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Er_present_d.set_copy_l
    {ω K K₀ X R J O Z A p T S q C W Y g D₀ a₀ f₀ H Γ
      ct Nt Tt z G Y₀ kt q₀ A' p' T' S' C' W' Z₀ v D₂ t B₀ CP t₀ σ τ ψ k : M.Domain}
    (model : Smem_d I ct Nt Tt) (hN : (smdl_structure_l I (R := Tt) model.1.2.1).Models KP)
    (w ξ ℓ K₁ X₁ β F D Q B e H₁ δ : (smdl_structure_l I (R := Tt) model.1.2.1).Domain)
    (source : Ep_source_d I ω ξ.val K X R) (owner : Ep_source_d I ω ξ.val K₀ Nt Tt)
    (numbers : Rr_layer_d I ω Nt Tt w.val z)
    (finite : Fseq_space_d (kp_pair_l hN) w ξ K₁) (support : Fseq_space_d (kp_pair_l hN) w ℓ H₁)
    (rank : V_d (kp_pair_l hN) δ X₁) (height : (smdl_structure_l I (R := Tt) model.1.2.1).IsLimitOrdinal δ)
    (hK : (smdl_structure_l I (R := Tt) model.1.2.1).mem K₁ X₁)
    (hβX : (smdl_structure_l I (R := Tt) model.1.2.1).mem β X₁)
    (common : ∀ n d f, M.mem n ω → Ep_space_d ξ.val n d → Fn0_d d β.val f → (M.mem f X ↔ M.mem f Nt))
    (hβ : M.mem β.val X) (family : Em_source_d ω ξ.val ℓ.val X F.val)
    (system : Ep_system_d I ω ξ.val ℓ.val X R F.val J O Z A p T S) (limit : Di_limit_d A p T S q C W)
    (wc : Wc_graph_d C W g) (bij : M.IsSetBijectionFromTo I g C Y)
    (ff : Fn0_d D₀ X f₀) (constant : Rs_const_d D₀ β.val f₀) (fv : Ep_repr_d q a₀ f₀ H)
    (hHΓ : Rd_entry_d H Γ g) (hΓ : M.TransitiveSet Γ)
    (owned : Eb_collapse_d w ξ ℓ K₁ X₁ β F D Q B e)
    (inside : M.MemberSubset G Nt)
    (digits : ∀ n m, Rd_entry_d n m z ↔ M.mem n ω ∧ n = m)
    (identity : ∀ x y, Rd_entry_d x y kt → x = y)
    (limit₀ : Di_limit_d A' p' T' S' q₀ C' W') (factor : Fn0_d C' Z₀ v)
    (values : ∀ a f E x, Ep_repr_d q₀ a f E → Rd_entry_d E x v → Ep_value_d q g a f x)
    (present : Er_present_d I ω ℓ.val Nt Tt z G Y₀ kt q₀ e.val D₂ t)
    (original : Fn0_d B₀ CP t₀) (copy : Fn0_d CP C' τ) (map : M.IsSetFunction I σ)
    (left : It_comp_d t₀ τ ψ) (right : It_comp_d σ t ψ) (composite : It_comp_d τ v k) :
    B.val = Γ ∧ (∀ x E, Rd_entry_d x E t → Rd_entry_d E x v) ∧
      ∀ x x' E, Rd_entry_d x x' σ → Rd_entry_d x E t₀ → Rd_entry_d E x' k := by
  have actual := owned.read_rank_l hZF model hN w ξ ℓ K₁ X₁ β F D Q B e H₁ δ owner numbers finite support
    rank height hK hβX
  obtain ⟨same, evaluation⟩ := actual.realize_l hZF source owner common hβ family system limit wc bij
    ff constant fv hHΓ hΓ
  -- 两次求值都使用同一个节点的同一支撑与函数，故同一集合像因子给出原坍塌值。
  have fixed x E (hxE : Rd_entry_d x E t) : Rd_entry_d E x v := by
    obtain ⟨u, _, hux, value⟩ := (present x E).mp hxE
    have entry := (rf_val_mem_l I hZF.1 owner.transitive model (hux.bounds_l I).2.2).mp hux
    obtain ⟨_, a, f, pair, actual⟩ := (evaluation u x).mp entry
    obtain ⟨a', f', pair', rep⟩ := value.read_mem_l hZF source.omega owner.transitive model inside digits identity
    obtain ⟨ha, hf⟩ := kpair_injective_l M pair' pair
    subst a' f'
    have hE : M.mem E C' := by
      obtain ⟨_, _, _, _, huE⟩ := rep
      exact (limit₀.projection.bound_l huE).2
    obtain ⟨y, _, hEy⟩ := factor.2.1 E hE
    have eq := (values a f E y rep hEy).unique_l hZF family system limit
      (fn0_of_function_l (ZF.modelsKP hZF) bij.1.1) actual
    exact eq ▸ hEy
  refine ⟨same, fixed, fun x x' E hxx hxE => ?_⟩
  -- 使用 into_set_l 返回的原复合图 k=v∘τ，不另选集合像复制。
  obtain ⟨E', _, hEE⟩ := copy.2.1 E (original.bound_l hxE).2
  obtain ⟨y, hxy, hyE⟩ := (right.2 x E').mp ((left.2 x E').mpr ⟨E, hxE, hEE⟩)
  have hxE' : Rd_entry_d x' E' t := map.2 x y x' hxy hxx ▸ hyE
  exact (composite.2 E x').mpr ⟨E', hEE, fixed x' E' hxE'⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原关系后继复制到工作模型中的实际集合像

原后继保持给定的关系码。其完整复制先进入小目标超幂，再经已构造的
集合像因子进入指定 j(A)。原活动边的常值方块保持，源良基性与下一步的
完整源条件均由实际目标回传，原后继无需先作隶属呈示。
工作目标的实际数字坐标和共同恒等图还将复制后的坐标值识别为原目标支撑。
一般原池求值保留同一个实际代表；返回的原复制 τ 与因子 v 满足实际复合方程 k=v∘τ。
工作侧小超幂及原关系复制均在入口内实际构造，所属目标的 KP 也由原图传输。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Er_graph_d.into_set_l
    {ω κ K L X R F J O Z A p T V q c C W d N S μ K' e i j c₀
      a₀ A₀ R₀ a₁ A₁ R₁ K₀
      Ls Ns Ts zs P RP ks Nt Tt zt kt π σ qs hs os CP UP js bs bt Γs Γt
      Js Os Zs Ds ps Vs Ws : M.Domain}
    (source : Ep_source_d I ω κ K X R) (target : Ep_source_d I ω μ K' N S)
    (small : Ep_source_d I ω κ K₀ A₀ R₀)
    (family : Em_source_d ω κ L X F) (coherent : Ec_source_d I ω κ L X F)
    (system : Ep_system_d I ω κ L X R F J O Z A p T V) (limit : Di_limit_d A p T V q C W)
    (model : Smdl_d I c C W) (hm : Smem_d I c₀ X R) (hn : Smem_d I d N S)
    (he : Smap_d I ω c d C N e) (hj : Smap_d I ω c₀ d X N j)
    (constants : Ep_constants_d X q i) (comp : It_comp_d i e j)
    (h₀ : Smem_d I a₀ A₀ R₀) (h₁ : Smem_d I a₁ A₁ R₁) (hA : Rd_entry_d A₀ A₁ j)
    (cover : Ea_subset_d ω κ X A₀)
    (ns : Smdl_d I bs Ns Ts) (nt : Smem_d I bt Nt Tt)
    (ownerMap : Smap_d I ω bs bt Ns Nt σ)
    (hNs : (smdl_structure_l I (R := Ts) ns.2.1).Models KP)
    (w ξ ℓ f : (smdl_structure_l I (R := Ts) ns.2.1).Domain)
    (hξ : Rd_entry_d ξ.val κ σ) (hℓ : Rd_entry_d ℓ.val L σ) (hf : Rd_entry_d f.val F σ)
    (numbers : Rr_layer_d I ω Ns Ts w.val zs) (numbers' : Rr_layer_d I ω Nt Tt ω zt)
    (digits : ∀ n m, Rd_entry_d n m zt ↔ M.mem n ω ∧ n = m)
    (fs : Fs_read_d ω Nt) (ownerTheory : Sc_theory_d I ω Nt Tt)
    (length : ∀ x, M.mem x Ls ↔ M.mem x Ns ∧ Rd_entry_d x ℓ.val Ts)
    (loc : It_local_d I w.val Ns Ts ξ.val ℓ.val f.val)
    (powers : ∀ m D : (smdl_structure_l I (R := Ts) ns.2.1).Domain,
      (smdl_structure_l I (R := Ts) ns.2.1).mem m w → Ep_space_d ξ m D →
        ∃ B, (smdl_structure_l I (R := Ts) ns.2.1).IsPowerSetOf B D)
    (parent : Smdl_d I hs P RP) (parentMap : Smap_d I ω hs a₀ P A₀ π)
    (px : Rf_ext_d I P RP) (theory : Sc_theory_d I ω P RP) (collection : Sc_collection_d I ω P RP)
    (agreement : Er_agree_d I ω Ns Ts ξ.val zs Γs P RP ks)
    (agreement' : Er_agree_d I ω Nt Tt κ zt Γt A₀ R₀ kt)
    (identity : ∀ x y, Rd_entry_d x y kt → x = y)
    (maps : Er_maps_d I ω Ns Ts ξ.val zs ks kt π σ)
    (smallDomains : ∀ n m D y, M.mem n ω → Rd_entry_d n m zs → Er_space_d I Ns Ts ξ.val m D →
      Rd_entry_d D y ks → Rf_small_d I P RP y)
    (raw : Er_graph_d I ω Ls Ns Ts ξ.val ℓ.val f.val zs P RP ks Js Os Zs Ds ps Vs Ws)
    (diagram : Di_system_d Js Os Ds ps Vs Ws) (rawLimit : Di_limit_d Ds ps Vs Ws qs CP UP)
    (original : Smdl_d I os CP UP) (fj : Fn0_d P CP js) (cj : Er_constants_d P qs js) :
    ∃ J₀ O₀ Z₀ D₀ p₀ T₀ V₀ q₀ c₁ C₀ W₀,
      Ep_system_d I ω κ L A₀ R₀ F J₀ O₀ Z₀ D₀ p₀ T₀ V₀ ∧
      Er_graph_d I ω L Nt Tt κ L F zt A₀ R₀ kt J₀ O₀ Z₀ D₀ p₀ T₀ V₀ ∧
      Di_limit_d D₀ p₀ T₀ V₀ q₀ C₀ W₀ ∧ Smdl_d I c₁ C₀ W₀ ∧
      Er_limit_d hZF ω Ls Ns Ts ξ.val f.val zs P RP ks L Nt Tt κ F zt A₀ R₀ kt π σ qs q₀ hs a₀ os CP UP c₁ C₀ W₀ ∧
    ∃ v k, Smap_d I ω c₁ a₁ C₀ A₁ v ∧ Smap_d I ω os a₁ CP A₁ k ∧
      (∀ a f E x, Ep_repr_d q₀ a f E → Rd_entry_d E x v → Ep_value_d q e a f x) ∧
      (∀ B x, Rd_entry_d B x k ↔ M.mem B CP ∧ ∃ u E, Rd_entry_d u B qs ∧
        Er_node_d I ω Ls Ns Ts ξ.val f.val zs P RP ks L Nt Tt κ F zt A₀ R₀ kt π σ q₀ u E ∧ Rd_entry_d E x v) ∧
      (∀ x x' B y, Rd_entry_d x x' π → Rd_entry_d x B js → Rd_entry_d x' y j → Rd_entry_d B y k) ∧
      Wf_rel_d CP UP ∧ It_source_d hZF ω os ∧ (∃ K₁, Ep_source_d I ω ω K₁ A₁ R₁) ∧
      (∀ a a' n B E x, Fn0_d n Ls a → Fn0_d n L a' → Smap_assign_d I n σ a a' →
        Er_seed_d I ω Ls Ns Ts ξ.val f.val zs P RP ks qs a B →
        Er_seed_d I ω L Nt Tt κ F zt A₀ R₀ kt q₀ a' E → Rd_entry_d E x v → Rd_entry_d B x k) ∧
      ((∀ α B, Ep_seed_d κ L q α B → Rd_entry_d B α e) →
        ∀ a a' n B E, Fn0_d n Ls a → Fn0_d n L a' → Smap_assign_d I n σ a a' →
          Er_seed_d I ω Ls Ns Ts ξ.val f.val zs P RP ks qs a B →
          Er_seed_d I ω L Nt Tt κ F zt A₀ R₀ kt q₀ a' E → Rd_entry_d B a' k) ∧
      (∀ Γ, M.MemberSubset Γ Nt →
        ∀ u E x, Er_eval_d I ω L Nt Tt zt Γ A₀ kt q₀ u E → Rd_entry_d E x v →
          ∃ a f, KPair_d M u a f ∧ Ep_value_d q e a f x) ∧
      ∃ τ, Smap_d I ω os c₁ CP C₀ τ ∧
        (∀ B E, Rd_entry_d B E τ ↔ M.mem B CP ∧ ∃ u, Rd_entry_d u B qs ∧
          Er_node_d I ω Ls Ns Ts ξ.val f.val zs P RP ks L Nt Tt κ F zt A₀ R₀ kt π σ q₀ u E) ∧
        It_comp_d τ v k := by
  have inside := source.transitive A₀ (hj.1.1.input_mem_of_pairMember hA)
  have agree : Ea_agree_d ω κ X A₀ := fun n D B hn hd sub => ⟨cover n D B hn hd sub, inside B⟩
  have family₀ := family.transfer_l agree
  have coherent₀ := coherent.transfer_l hZF agree
  -- 工作侧的小超幂在此实际构造；两种系统表示使用完全相同的对象和极限。
  obtain ⟨J₀, O₀, Z₀, D₀, p₀, T₀, V₀, q₀, c₁, C₀, W₀, system₀, limit₀, model₀, _⟩ :=
    ep_ultrapower_l hZF small family₀ coherent₀
  have hκt := ownerMap.1.1.output_mem_of_pairMember hξ
  have hLt := ownerMap.1.1.output_mem_of_pairMember hℓ
  have hFt := ownerMap.1.1.output_mem_of_pairMember hf
  have hNt := ownerMap.native_models_l hZF source.omega ns nt.1 hNs
  have raw₀ := system₀.toEp_graph_d.raw_l hZF fs nt ownerTheory small h₀ hκt hLt hFt
    numbers' digits agreement' identity family₀ coherent₀
  have length' x : M.mem x L ↔ M.mem x Nt ∧ Rd_entry_d x L Tt :=
    ⟨fun hx => ⟨fs.transitive L hLt x hx, (nt.2 x L).mpr ⟨fs.transitive L hLt x hx, hLt, hx⟩⟩,
      fun h => ((nt.2 x L).mp h.2).2.2⟩
  have copied := raw.copy_limit_l hZF source.omega ns nt.1 ownerMap hNs hNt w ξ ℓ f
    ⟨ω, fs.omega_mem⟩ ⟨κ, hκt⟩ ⟨L, hLt⟩ ⟨F, hFt⟩ hξ hℓ hf numbers numbers' length length' loc powers
    parent h₀.1 parentMap px theory collection agreement agreement' maps smallDomains raw₀
    diagram system₀.diagram rawLimit original limit₀ model₀
  refine ⟨J₀, O₀, Z₀, D₀, p₀, T₀, V₀, q₀, c₁, C₀, W₀, system₀, raw₀, limit₀, model₀, copied, ?_⟩
  obtain ⟨v, hv, values⟩ := ep_set_inclusion_l hZFC source target small family coherent system limit model hm hn he hj
    constants comp h₀ h₁ hA cover system₀ limit₀ model₀
  obtain ⟨τ, _, i₀, hτ, _, hi₀, _, ci₀, ts, _, square, _, _, seeds⟩ := copied
  obtain ⟨k, hk, ks⟩ := smap_comp_l I hZF hτ hv
  -- 小超幂的任意常值代表在指定大超幂中仍给出原活动边的同一个值。
  have constant x E y z (hxE : Rd_entry_d x E i₀) (hEy : Rd_entry_d E y v) (hxz : Rd_entry_d x z j) : y = z := by
    obtain ⟨a, D, f, ff, fc, fv⟩ := ci₀ x E hxE
    obtain ⟨_, n, hnω, fa, D', ds, fn⟩ := fv.source_l hZF family₀ system₀ limit₀
    have eq := fn.domain_eq_l hZF.1 ff
    subst D'
    have haJ := (system.indices a).mpr ((system₀.indices a).mp (fv.index_l hZF system₀ limit₀))
    obtain ⟨g, _, fg, gc, gv⟩ := ep_value_constant_l hZF source family system limit constants comp
      hnω haJ fa ds (hj.1.1.input_mem_of_pairMember hxz) hxz
    have eq := (ff.mono_target_l inside).ext_l hZF.1 fg (fun s hs => ⟨x, fc s hs, gc s hs⟩)
    exact (values a f E y fv hEy).unique_l hZF family system limit
      (fn0_of_function_l (ZF.modelsKP hZF) he.1.1) (eq.symm ▸ gv)
  have commute x x' B y (hxx : Rd_entry_d x x' π) (hxB : Rd_entry_d x B js) (hxy : Rd_entry_d x' y j) :
      Rd_entry_d B y k := by
    obtain ⟨E, hE, hBE⟩ := hτ.1.1.2.2 B (fj.bound_l hxB).2
    have hxE := (square js i₀ fj (fn0_of_function_l (ZF.modelsKP hZF) hi₀.1.1) cj ci₀ x x' B E hxx hxB).mp hBE
    obtain ⟨y₀, _, hEy⟩ := hv.1.1.2.2 E hE
    have hBy := (ks B y₀).mpr ⟨(fj.bound_l hxB).2, E, hBE, hEy⟩
    exact constant x' E y₀ y hxE hEy hxy ▸ hBy
  -- j↾A₀ 保持全部内部公式，故指定集合像继承完整源；再沿 k 回拉。
  have hR := ep_set_membership_l hZF source target hm hn hj h₀ h₁ hA
  obtain ⟨r, _, hr⟩ := ep_set_restriction_l hZF source target hm hn hj h₀.1 h₁.1 hA hR
  obtain ⟨_, smallω⟩ := small.rebase_l small.omega_mem (fun _ h => h)
    (small.cardinal_small.mono_mem_l I h₀ small.omega_mem small.below)
  have tr := smap_delta_l I hZF source.omega source.transitive target.transitive hm hn hj (n := 1)
    (Formula.isTransitive .newest) (by simp -implicitDefEqProofs) (Formula.isTransitive_delta0 _)
    ⟨fun _ => A₀, fun _ => A₀⟩ ⟨fun _ => A₁, fun _ => A₁⟩ (fun _ => hA)
  have trans := (Formula.satisfies_isTransitive_iff _ _).mp
    (tr.mp ((Formula.satisfies_isTransitive_iff _ _).mpr small.transitive))
  obtain ⟨K₁, next⟩ := (it_source_mem_l hZF h₀ smallω).image_mem_l hZF h₀.1 h₁ trans hr
  have native := (it_source_mem_l hZF h₁ next).pull_l hZF original h₁.1 hk
  -- 目标使用其实际隶属关系；良基性沿刚构造的同一图回传到原关系源。
  have wf : Wf_rel_d A₁ R₁ := by
    intro B _ ne
    obtain ⟨x, hx, minimal⟩ := KP.mem_minimal_exists_d (ZF.modelsKP hZF) ne
    exact ⟨x, hx, fun y hy edge => minimal y hy ((h₁.2 y x).mp edge).2.2⟩
  refine ⟨v, k, hv, hk, values, fun B x => ⟨?_, ?_⟩, commute,
    wf_of_map_l hZF wf (fn0_of_function_l (ZF.modelsKP hZF) hk.1.1)
      (fun a b x y edge ha hb => (hk.relation_l I hZF source.omega original h₁.1 ha hb).mp edge),
    native, ⟨K₁, next⟩, ?_, ?_, ?_, τ, hτ, ts, ?_⟩
  · intro hBx
    obtain ⟨hB, E, hBE, hEx⟩ := (ks B x).mp hBx
    obtain ⟨_, u, huB, node⟩ := (ts B E).mp hBE
    exact ⟨hB, u, E, huB, node, hEx⟩
  · rintro ⟨hB, u, E, huB, node, hEx⟩
    exact (ks B x).mpr ⟨hB, E, (ts B E).mpr ⟨hB, u, huB, node⟩, hEx⟩
  · intro a a' n B E x fa fa' assign first last hEx
    have hBE := seeds a a' n B E fa fa' assign first last
    exact (ks B x).mpr ⟨hτ.1.1.input_mem_of_pairMember hBE, E, hBE, hEx⟩
  · intro fixed
    -- 小目标的序数种子经同一因子进入大超幂，故仍由实际正常坍塌固定。
    have fixed₀ α B (seed : Ep_seed_d κ L q₀ α B) : Rd_entry_d B α v := by
      obtain ⟨n, a, i, D, f, fa, hi, ds, fc, rep⟩ := seed
      have hB : M.mem B C₀ := by
        obtain ⟨_, _, _, _, huB⟩ := rep
        exact (limit₀.projection.bound_l huB).2
      obtain ⟨x, _, hBx⟩ := hv.1.1.2.2 B hB
      obtain ⟨E, rep', hEx⟩ := values a f B x rep hBx
      have hEα := fixed α E ⟨n, a, i, D, f, fa, hi, ds, fc, rep'⟩
      exact he.1.1.1.2 E x α hEx hEα ▸ hBx
    intro a a' n B E fa fa' assign first last
    have hEa := last.collapse_l hZFC small family₀ coherent₀ system₀ limit₀ model₀ trans h₁ hv
      fixed₀ fs nt digits identity
    have hBE := seeds a a' n B E fa fa' assign first last
    exact (ks B a').mpr ⟨hτ.1.1.input_mem_of_pairMember hBE, E, hBE, hEa⟩
  · intro Γ subset u E x value hEx
    obtain ⟨a, f, pair, rep⟩ := value.read_mem_l hZF source.omega fs.transitive nt subset digits identity
    exact ⟨a, f, pair, values a f E x rep hEx⟩
  · exact ⟨hk.1.1.1.1, fun B x => (ks B x).trans ⟨And.right,
      fun ⟨E, hBE, hEx⟩ => ⟨hτ.1.1.input_mem_of_pairMember hBE, E, hBE, hEx⟩⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal
