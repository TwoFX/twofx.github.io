import VersoBlog
open Verso Genre Blog

set_option pp.rawOnError true

-- The root page of the blog directory, reachable at `/blog/`. The post list
-- itself is provided by the primary template via the "posts" parameter.
-- `showInNav := false` keeps it out of the top navigation (the `/posts/` page
-- is linked there instead, matching the old site).

#doc (Page) "Posts" =>

%%%
showInNav := false
%%%
