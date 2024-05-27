-- Basic definitions, imports and notation
import Prelude

-- Constructing interaction laws: Ch. 3
----------------------------------------------------------

-- Constructing functor-functor interaction laws: §3.1
import fil

-- The definition of monad-comonad interaction laws: §3.2
import MCIL.Core

-- Examples of functor-functor interaction laws: §3.4
import fil-examples

-- Biclosed monoidal categories §3.4.1
import Categories.Category.Monoidal.BiClosed

-- A computable example: §3.4.2
import concrete-examples

-- The category of functor-functor interaction laws: Ch. 4
----------------------------------------------------------
import IL

-- The definition of IL(𝒞): §4.1
import IL.Core

-- Properties of IL(𝒞): §4.2
import IL.Properties

-- Monoidal structure of IL(𝒞): §4.2.1
import IL.Monoidal

-- The category of monad-comonad interaction laws: §4.3
import MCIL.Core

-- Monad-comonad interaction laws are equivalent to monoids in IL(𝒞) : §4.4
import MCIL.Properties

-- Duality: Ch. 5
----------------------------------------------------------

-- A few facts about ends: §5.1.1 and §5.1.4  (some definitions, such as end-η existed before our changes)
import Categories.Diagram.End.Properties

-- Natural Transformations are an end: §5.1.3
import Categories.Diagram.End.Instances.NaturalTransformation

-- Fubini for ends : §5.1.5
import Categories.Diagram.End.Fubini

--Definition of the dual interaction law: §5.2
import IL.Dual

--Examples of duals
import IL.Dual.Examples
