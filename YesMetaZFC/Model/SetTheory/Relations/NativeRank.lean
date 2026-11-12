import YesMetaZFC.Model.SetTheory.Relations.OmegaCut
import YesMetaZFC.Model.SetTheory.Relations.Hierarchy
import YesMetaZFC.Model.SetTheory.Source.RankSizeInitial

/-! # 完整前驱解释保持实际秩历史

源中的原历史直接传入目标；父层的子集闭包排除所有外部反例。
本层直接搬运切片中的秩公式，不要求源模型满足 KP，也不要求层值具有小编号。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

theorem rr_native_rank_value_l {N R Γ C W H t A B : M.Domain}
    (nx : ∃ x, M.mem x N) (ny : ∃ y, M.mem y C)
    (ext : Extensional (smdl_structure_l I (R := W) ny))
    (U α V : (smdl_structure_l I (R := R) nx).Domain)
    (trans : (smdl_structure_l I (R := R) nx).TransitiveSet U)
    (carrier : ∀ x, M.mem x Γ ↔ M.mem x N ∧ M.PairMember I x U.val R)
    (ft : M.IsSetInjectionFromTo I t Γ C)
    (image : ∀ E, M.PairMember I E H W ↔ ∃ x, M.mem x Γ ∧ M.PairMember I x E t)
    (pred : ∀ x E, M.PairMember I x E t → ∀ P, M.PairMember I P E W ↔ ∃ y, M.PairMember I y x R ∧ M.PairMember I y P t)
    (closed : Rr_closed_d I C W H)
    (hα : (smdl_structure_l I (R := R) nx).mem α U)
    (hV : (smdl_structure_l I (R := R) nx).mem V U)
    (hαA : M.PairMember I α.val A t) (hVB : M.PairMember I V.val B t)
    (rank : Formula.satisfies
      (⟨Fin.cases ⟨V, hV⟩ (fun _ => ⟨α, hα⟩), fun _ => ⟨α, hα⟩⟩ :
        Env (rt_model_l U ⟨⟨α, hα⟩⟩) 2) (v_sigma_m (.bound 1) .newest)) :
    Rr_rank_d I C W A B := by
  let N₀ := smdl_structure_l I (R := R) nx
  let C₀ := smdl_structure_l I (R := W) ny
  let nu : Nonempty {x : N₀.Domain // N₀.mem x U} := ⟨⟨α, hα⟩⟩
  let a : C₀.Domain := ⟨A, ft.1.output_mem_of_pairMember hαA⟩
  let v : C₀.Domain := ⟨B, ft.1.output_mem_of_pairMember hVB⟩
  have domain (x : N₀.Domain) (hx : N₀.mem x U) := (carrier x.val).mpr ⟨x.property, hx⟩
  have down E P (hEH : M.PairMember I E H W) (hPE : M.PairMember I P E W) : M.PairMember I P H W := by
    obtain ⟨x, _, hxE⟩ := (image E).mp hEH
    obtain ⟨y, _, hyP⟩ := (pred x E hxE P).mp hPE
    exact (image P).mpr ⟨y, ft.1.input_mem_of_pairMember hyP, hyP⟩
  obtain ⟨⟨D, hD⟩, ⟨F, hF⟩, cert⟩ := rank
  obtain ⟨b₀, hb₀, hDb⟩ := ft.1.2.2 D.val (domain D hD)
  obtain ⟨f₀, hf₀, hFf⟩ := ft.1.2.2 F.val (domain F hF)
  let b : C₀.Domain := ⟨b₀, hb₀⟩
  let f : C₀.Domain := ⟨f₀, hf₀⟩
  let η : Env C₀ 2 := ⟨Fin.cases v (fun _ => a), fun _ => a⟩
  let ρ : Env (rt_model_l U nu) 2 := ⟨Fin.cases ⟨V, hV⟩ (fun _ => ⟨α, hα⟩), fun _ => ⟨α, hα⟩⟩
  let φ : Formula 1 5 := vc_matrix_m (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest
  have read (x : N₀.Domain) (hx : N₀.mem x U) (z : C₀.Domain) (hxz : M.PairMember I x.val z.val t) :
      Formula.satisfies (((η.push b).push f).push z) φ :=
    (rr_native_delta_l I nx ny U trans nu carrier ft pred φ (by simp -implicitDefEqProofs [φ])
      (vc_matrix_delta_l ..) (((ρ.push ⟨D, hD⟩).push ⟨F, hF⟩).push ⟨x, hx⟩)
      (((η.push b).push f).push z) (Fin.cases hxz (Fin.cases hFf (Fin.cases hDb (Fin.cases hVB (fun _ => hαA)))))).mp
        ((rt_model_delta_l trans nu (vc_matrix_delta_l ..)
          (((ρ.push ⟨D, hD⟩).push ⟨F, hF⟩).push ⟨x, hx⟩)).mp (cert ⟨x, hx⟩))
  have bH := (image b.val).mpr ⟨D.val, domain D hD, hDb⟩
  have vH := (image v.val).mpr ⟨V.val, domain V hV, hVB⟩
  refine ⟨a.property, v.property, ?_⟩
  change Formula.satisfies η (v_sigma_m (.bound 1) .newest)
  simp only [v_sigma_m, Formula.satisfies_exists_iff, Formula.satisfies_forall_iff]
  refine ⟨b, f, fun z => ?_⟩
  by_cases hz : M.PairMember I z.val H W
  · obtain ⟨x, hx, hxz⟩ := (image z.val).mp hz
    exact read ⟨x, ((carrier x).mp hx).1⟩ ((carrier x).mp hx).2 z hxz
  · have outside (β P : C₀.Domain) (hP : M.PairMember I P.val H W) : Vc_step_d β b f P z := by
      refine iff_of_false (fun h => hz (down P.val z.val hP h)) ?_
      rintro ⟨γ, _, Q, hQ, _, sub⟩
      exact hz (closed Q.val z.val Q.property z.property (down b.val Q.val bH hQ)
        (fun x hx => sub ⟨x, hx⟩))
    have base := read V hV v hVB
    simp only [φ, vc_matrix_m, Formula.satisfies_conj_iff, fn0_sat_l ext,
      Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff, rd_entry0_sat_l ext, vc_step_sat_l ext] at base ⊢
    exact ⟨base.1, base.2.1, fun β _ P hP _ => outside β P (down b.val P.val bH hP), outside a v vH⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 原关系切片上的全称秩识别与内在闭包

源内的整个秩历史和小编号经同一完整前驱图传输。目标在父层之外的对象
由子集闭包排除；父层内部的新子集则反向读取，覆盖全称秩公式的全部见证。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem rr_native_rank_l {N R Γ C W H t A B : M.Domain}
    (nx : ∃ x, M.mem x N) (ny : ∃ y, M.mem y C)
    (hN : (smdl_structure_l I (R := R) nx).Models KP)
    (ext : Extensional (smdl_structure_l I (R := W) ny))
    (U α V : (smdl_structure_l I (R := R) nx).Domain)
    (trans : (smdl_structure_l I (R := R) nx).TransitiveSet U)
    (carrier : ∀ x, M.mem x Γ ↔ M.mem x N ∧ Rd_entry_d x U.val R)
    (ft : M.IsSetInjectionFromTo I t Γ C)
    (image : ∀ E, Rd_entry_d E H W ↔ ∃ x, M.mem x Γ ∧ Rd_entry_d x E t)
    (pred : ∀ x E, Rd_entry_d x E t → ∀ P, Rd_entry_d P E W ↔ ∃ y, Rd_entry_d y x R ∧ Rd_entry_d y P t)
    (closed : Rr_closed_d I C W H)
    (hα : (smdl_structure_l I (R := R) nx).mem α U)
    (hV : (smdl_structure_l I (R := R) nx).mem V U)
    (hαA : Rd_entry_d α.val A t) (hVB : Rd_entry_d V.val B t)
    (rank : Vr_d U α V) (small : Sc_small_d U V) :
    Rr_rank_d I C W A B ∧ Rr_closed_d I C W B ∧ Rr_small_d I C W B := by
  let N₀ := smdl_structure_l I (R := R) nx
  let C₀ := smdl_structure_l I (R := W) ny
  let nu : Nonempty {x : N₀.Domain // N₀.mem x U} := ⟨⟨α, hα⟩⟩
  have domain (x : N₀.Domain) (hx : N₀.mem x U) := (carrier x.val).mpr ⟨x.property, hx⟩
  have full E : Rd_entry_d E B W ↔ ∃ x : N₀.Domain, N₀.mem x V ∧ Rd_entry_d x.val E t := by
    apply (pred V.val B hVB E).trans
    exact ⟨fun ⟨x, hx, hxE⟩ => ⟨⟨x, ((carrier x).mp (ft.1.input_mem_of_pairMember hxE)).1⟩, hx, hxE⟩,
      fun ⟨x, hx, hxE⟩ => ⟨x.val, hx, hxE⟩⟩
  have rank' := rr_native_rank_value_l I nx ny ext U α V
    trans carrier ft image pred closed hα hV hαA hVB
    ((vr_sat_l hN trans _ _ (.bound 1) .newest).mpr rank)
  refine ⟨rank', ?_, ?_⟩
  · intro E P hE hP hEB sub
    obtain ⟨x, hx, hxE⟩ := (full E).mp hEB
    have hEH := (image E).mpr ⟨x.val, ft.1.input_mem_of_pairMember hxE, hxE⟩
    obtain ⟨z, hz, hzP⟩ := (image P).mp (closed E P hE hP hEH sub)
    let z' : N₀.Domain := ⟨z, ((carrier z).mp hz).1⟩
    have subset : N₀.MemberSubset z' x := by
      intro y hy
      obtain ⟨Q, hQ, hyQ⟩ := ft.1.2.2 y.val (domain y (trans z' ((carrier z).mp hz).2 y hy))
      obtain ⟨u, hux, huQ⟩ := (pred x.val E hxE Q).mp (sub Q hQ ((pred z P hzP Q).mpr ⟨y.val, hy, hyQ⟩))
      have eq := ft.2 u y.val Q huQ hyQ
      subst u
      exact hux
    exact (full P).mpr ⟨z', rank.subset_mem_l trans hV hx ((carrier z).mp hz).2 subset, hzP⟩
  · intro E hE hEB
    obtain ⟨x, hx, hxE⟩ := (full E).mp hEB
    obtain ⟨μ, f, hμ, hf, index⟩ := small.mono_l ((rank.transitive_l trans hV) x hx)
    obtain ⟨m₀, hm₀, hμm⟩ := ft.1.2.2 μ.val (domain μ hμ)
    obtain ⟨f₀, hf₀, hff⟩ := ft.1.2.2 f.val (domain f hf)
    let m : C₀.Domain := ⟨m₀, hm₀⟩
    let g : C₀.Domain := ⟨f₀, hf₀⟩
    let η : Env C₀ 1 := ⟨fun _ => ⟨E, hE⟩, fun _ => ⟨E, hE⟩⟩
    let ρ : Env (rt_model_l U nu) 3 :=
      ⟨Fin.cases ⟨f, hf⟩ (Fin.cases ⟨μ, hμ⟩ (fun _ => ⟨x, trans V hV x hx⟩)), fun _ => ⟨α, hα⟩⟩
    have valid : Formula.satisfies (image_env_l Subtype.val ρ) (sc_index_m (.bound 1) (.bound 2) .newest) :=
      (sc_index_sat_l hN ..).mpr index
    refine ⟨hE, ?_⟩
    change Formula.satisfies η (sc_small_m .newest)
    simp only [sc_small_m, Formula.satisfies_exists_iff]
    refine ⟨m, g, ?_⟩
    exact (rr_native_delta_l I nx ny U trans nu carrier ft pred
      (sc_index_m (.bound 1) (.bound 2) .newest) (by simp -implicitDefEqProofs) (sc_index_delta_l ..)
      ρ ((η.push m).push g) (Fin.cases hff (Fin.cases hμm (fun _ => hxE)))).mp valid

end YesMetaZFC.SetTheory.Internal
