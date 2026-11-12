import YesMetaZFC.Model.SetTheory.ReducedPower.RelationNormalize
import YesMetaZFC.Model.SetTheory.ReducedPower.RelationCopyPull
import YesMetaZFC.Model.SetTheory.Relations.CollectCode
import YesMetaZFC.SetTheory.Card.OrdinalImage

/-! # 原关系超幂分量中幂集像的可数性

原幂集的每个新商成员先规范化为处处取子集值的内部函数。
内部函数空间由单个旧子集编码；实际商投影将这份可数代码族满射到
幂集像的整个成员载体。这里不要求原模型可数，也不要求商良基。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel FilterZF
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Rp_model_d.power_count_l {Ω c Y S D t U G o p C T A B : M.Domain}
    (hΩ : M.IsOmega Ω) (source : Smdl_d I c Y S) (ext : Rf_ext_d I Y S)
    (theory : Sc_theory_d I Ω Y S)
    (native : (smdl_structure_l I (R := S) source.2.1).Models ZF)
    (ω δ d P : (smdl_structure_l I (R := S) source.2.1).Domain)
    (hω : (smdl_structure_l I (R := S) source.2.1).IsOmega ω)
    (hδ : (smdl_structure_l I (R := S) source.2.1).IsInfiniteCardinal (kp_pair_l (ZF.modelsKP native)) ω δ)
    (small : (smdl_structure_l I (R := S) source.2.1).CardinalLessOrEqual (kp_pair_l (ZF.modelsKP native)) d δ)
    (power : (smdl_structure_l I (R := S) source.2.1).IsPowerSetOf P δ)
    (carrier : ∀ x, M.mem x B ↔ M.mem x Y ∧ Rd_entry_d x P.val S)
    (count : M.CardinalLessOrEqual I B Ω)
    (ft : Fn0_d D Y t) (domain : ∀ s x, Rd_entry_d s x t → Rd_entry_d x d.val S)
    (base : Base_d D U) (proper : Proper_d U) (family : Rc_family_d I Y S D d.val t G)
    (model : Rp_model_d I D Y U S o G p C T)
    (value : ∃ f, M.mem f G ∧ Rs_const_d D P.val f ∧ Rd_entry_d f A p) :
    ∃ H, (∀ x, M.mem x H ↔ M.mem x C ∧ Rd_entry_d x A T) ∧ M.CardinalLessOrEqual I H Ω := by
  let N := smdl_structure_l I (R := S) source.2.1
  have hN := ZF.modelsKP native
  have codes := (rc_family_native_l I source.2.1 hN.1 d ft).mp family
  obtain ⟨F,K,space,inputs,countK⟩ := rr_power_function_count_l hZF source.2.1 native
    ω δ d P hω hδ small power carrier count
  let χ : UnarySchema 2 := { body := rd_entry0_m .newest (.bound 1) (.bound 2) }
  obtain ⟨H,hH⟩ := ZF.separation_exists_d hZF χ ⟨Fin.cases A (fun _ => T),fun _ => C⟩ C
  have members x : M.mem x H ↔ M.mem x C ∧ Rd_entry_d x A T :=
    (hH x).trans (and_congr_right fun _ => rd_entry0_sat_l hZF.1 ..)
  let ρ : Env M 5 := ⟨fun i => [Y,S,t,G,p].get i,fun _ => Y⟩
  let φ : BinarySchema 5 := {
    body := Formula.existsMem (.bound 5)
      (.conj (rc_graph_m (𝒞 := kpair_convention_l) (.bound 3) (.bound 4) (.bound 5) (.bound 2) .newest)
        (rd_entry0_m .newest (.bound 1) (.bound 7))) }
  have sat f E : φ.denote ρ f E ↔ ∃ g, M.mem g G ∧ Rc_graph_d I Y S t f g ∧ Rd_entry_d g E p := by
    simp only [φ,BinarySchema.denote,Formula.satisfies_existsMem_iff,Formula.satisfies_conj_iff,
      rc_graph_sat_l I hZF.1,rd_entry0_sat_l hZF.1]
    rfl
  have function f (hf : M.mem f K) : Fn0_d d P (⟨f,((inputs f).mp hf).1⟩ : N.Domain) :=
    fn0_of_function_l hN ((space _).mp ((inputs f).mp hf).2)
  have total f (hf : M.mem f K) : ∃ E, φ.denote ρ f E := by
    let f' : N.Domain := ⟨f,((inputs f).mp hf).1⟩
    obtain ⟨g,fg,read⟩ := smdl_function_l hZF source.2.1 hN.1 d P f' (function f hf) ft domain
    have graph := (rc_graph_native_l I source.2.1 hN.1 ft fg f').mpr read
    have hg := (codes g).mpr ⟨fg,P,f',function f hf,read⟩
    obtain ⟨E,_,gE⟩ := model.map.projection.2.2 g hg
    exact ⟨E,(sat f E).mpr ⟨g,hg,graph,gE⟩⟩
  have unique f (_ : M.mem f K) E E' (h : φ.denote ρ f E) (h' : φ.denote ρ f E') : E = E' := by
    obtain ⟨g,hg,graph,gE⟩ := (sat f E).mp h
    obtain ⟨g',hg',graph',gE'⟩ := (sat f E').mp h'
    have eq := graph.unique_l I hZF.1 ft (model.map.functions g hg) (model.map.functions g' hg') graph'
    exact model.map.projection.1.2 g E E' gE (eq.symm ▸ gE')
  have target f E (hf : M.mem f K) (h : φ.denote ρ f E) : M.mem E H := by
    obtain ⟨g,hg,graph,gE⟩ := (sat f E).mp h
    obtain ⟨k,hk,constant,kA⟩ := value
    have fg := model.map.functions g hg
    have read := (rc_graph_native_l I source.2.1 hN.1 ft fg
      (⟨f,((inputs f).mp hf).1⟩ : N.Domain)).mp graph
    refine (members E).mpr ⟨model.map.projection.output_mem_of_pairMember gE,
      (model.relation g k E A gE kA).mpr ⟨D,base.top,?_⟩⟩
    intro s hs
    obtain ⟨x,hx,sx⟩ := ft.2.1 s hs
    obtain ⟨y,hy,sy⟩ := fg.2.1 s hs
    exact ⟨y,hy,P.val,P.property,sy,constant s hs,
      ((function f hf).bound_l ((read s ⟨x,hx⟩ ⟨y,hy⟩ sx).mp sy)).2⟩
  obtain ⟨q,fq,law⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ total unique target
  have onto E (hE : M.mem E H) : ∃ f, M.mem f K ∧ Rd_entry_d f E q := by
    obtain ⟨g,hg,gE,_,f,ff,graph⟩ := rc_bounded_representative_l hZF hΩ source ext theory
      d ft domain base proper codes model ⟨P.property,value⟩ ((members E).mp hE).2
    have hf := (inputs f.val).mpr ⟨f.property,(space f).mpr (fn0_function_l hN ff)⟩
    exact ⟨f.val,hf,(law f.val E).mpr ⟨hf,(sat f.val E).mpr ⟨g,hg,graph,gE⟩⟩⟩
  exact ⟨H,members,ZF.ordinal_image_bound_l I hZF (hΩ.isOrdinal (ZF.modelsKP hZF)) countK fq onto⟩

end YesMetaZFC.SetTheory.Internal
