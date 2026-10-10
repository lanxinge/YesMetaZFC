import YesMetaZFC.Model.SetTheory.Internal.DirectedSystem.FiniteCover
import YesMetaZFC.Model.SetTheory.Internal.DirectedSystem.Elementary
import YesMetaZFC.Model.SetTheory.Internal.DirectedSystem.Factor
import YesMetaZFC.Model.SetTheory.Internal.EmbeddingSource

/-! # 完整初等锥在定向极限上的唯一初等因子

任意内部公式仅用内部有限支撑。先把这组参数推到一个共同分量，再比较
该分量的极限嵌入和锥映射，得到全部内部代码的初等性。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem di_factor_elementary_l {ω J L A p T R q c C V d Y W f : M.Domain}
    (hω : M.IsOmega ω) (h : Di_system_d J L A p T R) (limit : Di_limit_d A p T R q C V)
    (elementary : Di_elementary_d I ω L A p T R) (model : Smdl_d I c C V) (target : Smdl_d I d Y W)
    (hf : Fn0_d A Y f)
    (comm : ∀ x y u v, Rd_entry_d x y T → Rd_entry_d x u f → Rd_entry_d y v f → u = v)
    (cone : ∀ i e X S, Di_stage_d I A p R i e X S → ∃ k, Smap_d I ω e d X Y k ∧
      ∀ x y, Rd_entry_d x y k ↔ M.mem x X ∧ Rd_entry_d x y f) :
    ∃ g, Smap_d I ω c d C Y g ∧
      (∀ x B y, Rd_entry_d x B q → Rd_entry_d x y f → Rd_entry_d B y g) ∧
      ∀ k, Fn0_d C Y k → (∀ x B y, Rd_entry_d x B q → Rd_entry_d x y f → Rd_entry_d B y k) → k = g := by
  have fiber x y i u v (hx : Rd_entry_d x i p) (hy : Rd_entry_d y i p)
      (hxu : Rd_entry_d x u f) (hyv : Rd_entry_d y v f) :
      (x = y ↔ u = v) ∧ (Rd_entry_d x y R ↔ Rd_entry_d u v W) := by
    obtain ⟨e, X, S, stage⟩ := di_stage_exists_l hZF h hx
    obtain ⟨k, hk, spec⟩ := cone i e X S stage
    have hxX := (stage.2.1 x).mpr ⟨(h.index.bound_l hx).1, hx⟩
    have hyX := (stage.2.1 y).mpr ⟨(h.index.bound_l hy).1, hy⟩
    have hxk := (spec x u).mpr ⟨hxX, hxu⟩
    have hyk := (spec y v).mpr ⟨hyX, hyv⟩
    exact ⟨⟨fun e => hk.1.1.1.2 y u v (e ▸ hxk) hyk, fun e => hk.1.2 x y v (e ▸ hxk) hyk⟩,
      (⟨fun hr => (stage.2.2 x y).mpr ⟨hxX, hyX, hr⟩, fun hr => ((stage.2.2 x y).mp hr).2.2⟩ :
        Rd_entry_d x y R ↔ Rd_entry_d x y S).trans (hk.relation_l I hZF hω stage.1 target hxk hyk)⟩
  obtain ⟨g, hg, law, _, unique⟩ := di_factor_embedding_l hZF h limit hf comm fiber
  obtain ⟨Z, hZ⟩ := scode_exists_l I hZF hω
  obtain ⟨E, hE⟩ := ZF.exists_functionSpace hZF I ω C
  obtain ⟨K, hK⟩ := ZF.exists_functionSpace hZF I ω Y
  refine ⟨g, ⟨hg, Z, hZ, fun z u v hz hu hv huv => ?_⟩, law, unique⟩
  obtain ⟨n, F, r, code⟩ := (hZ z).mp hz
  obtain ⟨b, hb, bound⟩ := sbound_exists_l I hZF hω code.2.1
  have bω := hω.transitive hZF b hb
  obtain ⟨i, e, X, S, a, stage, ha, cover⟩ := di_finite_cover_l hZF hω h limit hb (fn0_of_function_l (ZF.modelsKP hZF) hu)
  obtain ⟨s, hs, ss⟩ := di_elementary_limit_l hZF hω h limit elementary stage model
  obtain ⟨t, ht, ts⟩ := cone i e X S stage
  have haω := fn0_function_l (ZF.modelsKP hZF) ha
  obtain ⟨u₀, hu₀, aus⟩ := smap_assign_exists_l I hZF hs.1.1 haω
  obtain ⟨v₀, hv₀, avt⟩ := smap_assign_exists_l I hZF ht.1.1 haω
  have agree {D f g : M.Domain} (hf : M.IsSetFunctionFromTo I f ω D) (hg : M.IsSetFunctionFromTo I g ω D)
      (forward : ∀ i x, M.mem i b → Rd_entry_d i x f → Rd_entry_d i x g) : Senv_agree_d I b f g := by
    intro i x hi
    refine ⟨forward i x hi, fun hx => ?_⟩
    obtain ⟨y, _, hy⟩ := hf.2.2 i (bω i hi)
    exact hg.1.2 i y x (forward i y hi hy) hx ▸ hy
  have left := agree hu hu₀ (fun j B hj hjB => by
    obtain ⟨x, hx, hjx⟩ := ha.2.1 j (bω j hj)
    exact aus j (bω j hj) x B hjx ((ss x B).mpr ⟨hx, cover j x B hj hjx hjB⟩))
  have right := agree hv hv₀ (fun j y hj hjy => by
    obtain ⟨B, _, hjB⟩ := hu.2.2 j (bω j hj)
    obtain ⟨x, hx, hjx⟩ := ha.2.1 j (bω j hj)
    obtain ⟨y₀, _, hxy⟩ := ht.1.1.2.2 x hx
    have hBy := law x B y₀ (cover j x B hj hjx hjB) ((ts x y₀).mp hxy).2
    have eq := hv.1.2 j y₀ y (huv j (bω j hj) B y₀ hjB hBy) hjy
    exact eq ▸ avt j (bω j hj) x y₀ hjx hxy)
  obtain ⟨H, hH⟩ := ZF.exists_functionSpace hZF I ω X
  have old := hs.ssat_l I hZF.1 stage.1 model code.2.1 code.2.2 hH hE ((hH a).mpr haω) ((hE u₀).mpr hu₀) aus
  have next := ht.ssat_l I hZF.1 stage.1 target code.2.1 code.2.2 hH hK ((hH a).mpr haω) ((hK v₀).mpr hv₀) avt
  exact (satisfies_decode_l I hZF.1 model code hE).trans
    ((ssat_agree_l I hZF code.2.1 bound hE code.2.2 ((hE u).mpr hu) ((hE u₀).mpr hu₀) left).trans
      (old.symm.trans (next.trans ((ssat_agree_l I hZF code.2.1 bound hK code.2.2
        ((hK v).mpr hv) ((hK v₀).mpr hv₀) right).symm.trans (satisfies_decode_l I hZF.1 target code hK).symm))))

end YesMetaZFC.SetTheory.Internal
