import YesMetaZFC.Model.SetTheory.Internal.FiniteConjunction
import YesMetaZFC.Model.SetTheory.Internal.RankLargest
import YesMetaZFC.Model.SetTheory.Internal.Compiler
import YesMetaZFC.Model.SetTheory.Internal.Sigma1Substructure

/-! # 前驱定义域的实际内部公式

先合取任意内部有限组变量的成员断言，再追加原公式“X=Vν，其中 ν 最大”，
最后绑定 X。程序本身不依赖实现元组、背景秩层或任何真值假设。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

/-- 原变量数来自内部 ω；前一层只是新绑定变量，未增添类型常量。 -/
theorem sg_guard_build_l (hZF : M.Models ZF) {ω n : M.Domain} (hω : M.IsOmega ω) (hn : M.mem n ω) :
    ∃ a m G u, Sformula_d I ω a m G u ∧
      ∀ c Y R (hm : Smem_d I c Y R) f, M.IsSetFunctionFromTo I f ω Y →
        (Satisfies_d I ω c a f ↔ ∃ X, ∃ hx : M.mem X Y,
          Formula.satisfies (⟨fun _ => ⟨X, hx⟩, fun _ => ⟨X, hx⟩⟩ :
            Env (smdl_structure_l I (R := R) hm.1.2.1) 1) (sv_last_m .newest) ∧
          ∀ i y, M.mem i n → M.PairMember I i y f → M.mem y X) := by
  obtain ⟨m, G, u, hG, hu, all⟩ := sg_all_build_l I hZF hω hn hn
  obtain ⟨b, succ, hb⟩ := hω.1.2 n hn
  let φ : Formula 1 1 := sv_last_m .newest
  have hc : φ.FreeClosed := sv_last_m_freeClosed _ rfl
  obtain ⟨m₁, G₁, v, add, compile⟩ := source_compile_core_l I hZF hω (source_core_l φ)
    (source_core_closed_l φ hc) (fun _ => n) hb (fun _ => succ.predecessor_mem) hG
  obtain ⟨m₂, G₂, w, conj, both⟩ := sfm_and_l I hZF hω add.program (add.span u hu) add.root
  obtain ⟨l, H, r, ex, quant⟩ := sfm_ex_l I hZF hω conj.program hn conj.root
  obtain ⟨a, ca⟩ := I.total H r
  have form : Sformula_d I ω a l H r := ⟨ca, ex.program, ex.root⟩
  refine ⟨a, l, H, r, form, fun c Y R hm f fn => ?_⟩
  obtain ⟨E, hE⟩ := ZF.exists_functionSpace hZF I ω Y
  have hf := (hE f).mpr fn
  have body X (hx : M.mem X Y) g (update : Senv_update_d I f n X g) :
      Ssat_d I Y R E G₂ m₂ w g ↔
        Formula.satisfies (⟨fun _ => ⟨X, hx⟩, fun _ => ⟨X, hx⟩⟩ :
          Env (smdl_structure_l I (R := R) hm.1.2.1) 1) φ ∧
          ∀ i y, M.mem i n → M.PairMember I i y f → M.mem y X := by
    have fg := update.function_l I fn hn hx
    have hg := (hE g).mpr fg
    have hbg := (update.2 n X).mpr (Or.inl ⟨rfl, rfl⟩)
    have agree := update.agree_l I (KP.mem_irrefl_d (ZF.modelsKP hZF) n)
    let ρ : Env (smdl_structure_l I (R := R) hm.1.2.1) 1 := ⟨fun _ => ⟨X, hx⟩, fun _ => ⟨X, hx⟩⟩
    have base := (compile Y R hm.1.2.1 E hE g hg ρ (fun _ => hbg)).trans (source_core_sat_l φ ρ)
    have old := (add.sat_l I hZF hG hu Y R E g).symm.trans (all Y R E g X hE hg hbg)
    refine (both Y R E g hg).trans ((and_congr old base).trans ⟨?_, ?_⟩)
    · rintro ⟨members, truth⟩
      exact ⟨truth, fun i y hi he => ((hm.2 y X).mp (members i y hi ((agree i y hi).mp he))).2.2⟩
    · rintro ⟨truth, members⟩
      exact ⟨fun i y hi he => (hm.2 y X).mpr ⟨fg.output_mem_of_pairMember he, hx,
        members i y hi ((agree i y hi).mpr he)⟩, truth⟩
  refine (satisfies_decode_l I hZF.1 hm.1 form hE).trans ((quant Y R E f hf).trans ⟨?_, ?_⟩)
  · rintro ⟨X, g, hx, update, truth⟩
    exact ⟨X, hx, (body X hx g update).mp truth⟩
  · rintro ⟨X, hx, truth⟩
    obtain ⟨g, update, _⟩ := senv_update_exists_l I hZF fn hn hx
    exact ⟨X, g, hx, update, (body X hx g update).mpr truth⟩

/-- 在后继秩层上，该实际公式恰检查所有原变量是否属于前一层。 -/
theorem sg_guard_rank_l (hZF : M.Models ZF) {ω n : M.Domain} (hω : M.IsOmega ω) (hn : M.mem n ω) :
    ∃ a m G u, Sformula_d I ω a m G u ∧
      ∀ ν μ X Y c R f, V_d I ν X → V_d I μ Y → M.SuccessorOf μ ν → M.MemberSubset ω ν →
        Smem_d I c Y R → M.IsSetFunctionFromTo I f ω Y →
        (Satisfies_d I ω c a f ↔ ∀ i y, M.mem i n → M.PairMember I i y f → M.mem y X) := by
  obtain ⟨a, m, G, u, form, guard⟩ := sg_guard_build_l I hZF hω hn
  refine ⟨a, m, G, u, form, fun ν μ X Y c R f hV hW hs hων hm fn => ?_⟩
  have pow := ZF.v_successor_l I hZF hV hW hs
  have hXY := (pow X).mpr (fun _ h => h)
  have hwY := (pow ω).mpr (fun i hi => ZF.v_ordinal_mem_l I hZF hV (hων i hi))
  let N := rt_model_l Y ⟨⟨ω, hwY⟩⟩
  have last Z (hZ : M.mem Z Y) :
      Formula.satisfies (⟨fun _ => ⟨Z, hZ⟩, fun _ => ⟨Z, hZ⟩⟩ :
        Env (smdl_structure_l I (R := R) hm.1.2.1) 1) (sv_last_m .newest) ↔ Z = X := by
    let ρ : Env N 1 := ⟨fun _ => ⟨Z, hZ⟩, fun _ => ⟨Z, hZ⟩⟩
    exact (smem_formula_l I hm ⟨⟨ω, hwY⟩⟩ (sv_last_m .newest) ρ).symm.trans
      (sv_last_rank_l I hZF hω hV hW hs hwY ρ .newest)
  refine (guard c Y R hm f fn).trans ⟨?_, ?_⟩
  · rintro ⟨Z, hZ, hz, all⟩
    exact (last Z hZ).mp hz ▸ all
  · intro all
    exact ⟨X, hXY, (last X hXY).mpr rfl, all⟩

end YesMetaZFC.SetTheory.Internal
